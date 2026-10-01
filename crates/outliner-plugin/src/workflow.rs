//! The workflow activity that outlines matched patterns during function analysis.

use std::collections::HashSet;
use std::sync::Mutex;
use std::time::Instant;

use binaryninjacore_sys::*;
use outliner_core::fused::find_fused_matches;
use outliner_core::matcher::{arg_var_set, find_matches, Round};
use outliner_core::plan::build_plan;
use outliner_core::sites::find_expression_sites;
use serde::Serialize;

use crate::env::BnEnv;
use crate::ffi::{cstr, log_debug, log_error, log_info, log_warn, Func, Mlil, View};
use crate::rewrite::{apply_plan, record_references, Target};
use crate::snapshot;
use crate::store;
use crate::types::TypeTable;

pub const ACTIVITY_NAME: &str = "extension.outliner.outlinePatterns";
pub const BASE_WORKFLOW: &str = "core.function.metaAnalysis";
/// The activity runs right before HLIL generation, so patterns are matched
/// against the final MLIL, i.e. what the MLIL view shows.
pub const ANCHOR_ACTIVITY: &str = "core.function.generateHighLevelIL";
const FALLBACK_ANCHOR: &str = "core.function.generateMediumLevelIL";

pub const SETTING_RETYPE: &str = "outliner.retypeResult";
/// Patterns may refer to calls produced by earlier rounds (a `substr` after an
/// `rfind` takes four), and a chain of destructors whose flag tests are
/// tail-duplicated unfuses one per round.
pub const MAX_ROUNDS: usize = 12;

const ACTIVITY_CONFIG: &str = r#"{"name":"extension.outliner.outlinePatterns","title":"Outliner: Outline Inlined Patterns","description":"Replace user-defined MLIL patterns (inlined functions) with calls to a function of the given signature.","eligibility":{"auto":{"default":true}}}"#;

const SETTING_RETYPE_PROPERTIES: &str = r#"{"title":"Retype Result Variables","type":"boolean","default":true,"description":"Give the variable that receives an outlined call's result the return type of the call's signature when its current type differs."}"#;

/// Wall-clock laps.
pub struct Clock {
    last: Instant,
}

impl Clock {
    pub fn start() -> Clock {
        Clock { last: Instant::now() }
    }

    /// Seconds since the previous lap.
    pub fn lap(&mut self) -> f64 {
        let now = Instant::now();
        let seconds = now.duration_since(self.last).as_secs_f64();
        self.last = now;
        seconds
    }
}

/// One record per activity invocation: where the time went, for the timing
/// report to summarise after a reanalysis.  Every phase is wall-clock seconds.
#[derive(Clone, Debug, Default, Serialize)]
pub struct Stats {
    pub function: String,
    pub instructions: usize,
    pub rounds: usize,
    pub outlined: usize,
    pub patterns: f64,
    pub setup: f64,
    pub view: f64,
    pub plain: f64,
    pub fused: f64,
    pub sites: f64,
    pub apply: f64,
    pub finish: f64,
    pub apply_build: f64,
    pub apply_finalize: f64,
    pub apply_ssa: f64,
    pub apply_commit: f64,
    pub apply_retype: f64,
    pub total: f64,
    /// What each round found and outlined.
    pub summary: Vec<String>,
}

pub static STATS: Mutex<Vec<Stats>> = Mutex::new(Vec::new());

pub fn reset_stats() {
    STATS.lock().unwrap_or_else(|e| e.into_inner()).clear();
}

pub fn take_stats() -> Vec<Stats> {
    STATS.lock().unwrap_or_else(|e| e.into_inner()).clone()
}

unsafe extern "C" fn outline_action(_ctxt: *mut std::os::raw::c_void, context: *mut BNAnalysisContext) {
    let result = std::panic::catch_unwind(|| outline(context));
    if let Err(panic) = result {
        let message = panic
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_else(|| "unknown panic".to_string());
        log_error(&format!("Outliner failed: {message}"));
    }
}

fn retype_setting(view: &View) -> bool {
    unsafe {
        let settings = BNCreateSettings(cstr("default").as_ptr());
        if settings.is_null() {
            return true;
        }
        let value = BNSettingsGetBool(settings, cstr(SETTING_RETYPE).as_ptr(), view.raw(), std::ptr::null_mut(), std::ptr::null_mut());
        BNFreeSettings(settings);
        value
    }
}

fn outline(context: *mut BNAnalysisContext) {
    let started = Instant::now();
    let mut clock = Clock::start();
    let Some(func) = (unsafe { Func::owned(BNAnalysisContextGetFunction(context)) }) else { return };
    let Some(view) = func.view() else { return };
    let compiled = store::compiled_patterns(&view);
    if compiled.patterns.is_empty() {
        return;
    }
    let mut stats = Stats { function: func.name(), ..Default::default() };
    stats.patterns = clock.lap();
    match outline_function(context, &view, &func, &compiled, &mut stats, &mut clock) {
        Ok(()) => {}
        Err(e) => log_error(&format!("Outliner failed on {}: {e}", stats.function)),
    }
    stats.total = started.elapsed().as_secs_f64();
    STATS.lock().unwrap_or_else(|e| e.into_inner()).push(stats);
}

fn outline_function(
    context: *mut BNAnalysisContext,
    view: &View,
    func: &Func,
    compiled: &store::Compiled,
    stats: &mut Stats,
    clock: &mut Clock,
) -> Result<(), String> {
    let patterns = &compiled.patterns;
    let rules = &compiled.rules;
    let retype = retype_setting(view);
    let targets: Vec<Option<Target>> =
        patterns.iter().map(|p| store::resolve_target(view, p).map(|(addr, ty)| Target { addr, ty })).collect();
    let has_target: Vec<bool> = targets.iter().map(Option::is_some).collect();
    let env = BnEnv::new(view.clone(), func, TypeTable::default());
    let mut total = 0usize;
    let mut summary: Vec<String> = Vec::new();
    let mut warned: HashSet<usize> = HashSet::new();
    let mut original: Option<Mlil> = None;
    stats.setup = clock.lap();
    for round_no in 0..MAX_ROUNDS {
        let Some(mlil) = (unsafe { Mlil::owned(BNAnalysisContextGetMediumLevelILFunction(context)) }) else { break };
        if round_no == 0 {
            original = Some(mlil.clone());
        }
        stats.rounds = round_no + 1;
        env.begin_round(mlil.clone());
        // The matchers work on a snapshot of the round's MLIL; it is dropped with the round.
        let snap = {
            let mut types = env.types.borrow_mut();
            snapshot::read(&mlil, func, &mut types)
        };
        let f = &snap.f;
        if round_no == 0 {
            stats.instructions = f.len();
        }
        stats.view += clock.lap();
        let (matches, fused, sites) = {
            let round = Round::new(f, &env);
            // Plain shapes first (they reuse the result variable), then fused
            // guards in the blocks nothing else claimed, then expression sites.
            let matches = find_matches(&round, patterns, rules, None);
            let mut claimed = f.block_set();
            let mut deleted = f.instr_set();
            for m in &matches {
                for start in m.own_blocks.iter().chain(&m.internal_blocks) {
                    if let Some(b) = f.block_at(*start) {
                        claimed.insert(b.id.0 as usize);
                    }
                }
                deleted.union_with(&m.deleted);
            }
            let mut live = arg_var_set(f, &matches, patterns);
            stats.plain += clock.lap();
            let fused = find_fused_matches(&round, patterns, rules, Some(&claimed), &deleted, &live);
            for fm in &fused {
                for start in &fm.blocks_touched {
                    if let Some(b) = f.block_at(*start) {
                        claimed.insert(b.id.0 as usize);
                    }
                }
                deleted.union_with(&fm.deleted);
                for call in &fm.calls {
                    let pattern = &patterns[call.pattern];
                    for id in pattern.param_ids().into_iter().flatten() {
                        if let Some(b) = call.binding(id) {
                            for v in b.reads(f) {
                                live.insert(v.0 as usize);
                            }
                        }
                    }
                }
            }
            stats.fused += clock.lap();
            let sites = find_expression_sites(&round, patterns, rules, Some(&claimed), &deleted, &live);
            stats.sites += clock.lap();
            (matches, fused, sites)
        };
        let found = format!("{} plain, {} fused, {} site(s)", matches.len(), fused.len(), sites.len());
        log_debug(&format!("{} round {}: {found}", f.name, round_no + 1));
        if matches.is_empty() && fused.is_empty() && sites.is_empty() {
            break;
        }
        let used: Vec<usize> = matches
            .iter()
            .map(|m| m.pattern)
            .chain(fused.iter().flat_map(|fm| fm.calls.iter().map(|c| c.pattern)))
            .chain(sites.iter().map(|s| s.pattern))
            .collect();
        for p in &used {
            if !has_target[*p] && warned.insert(*p) {
                log_warn(&format!("no call target registered for pattern {:?}; skipping", patterns[*p].name));
            }
        }
        let plan = build_plan(f, patterns, &matches, &fused, &sites, &has_target, retype)?;
        if plan.is_empty() {
            break;
        }
        let (count, times) = {
            let types = env.types.borrow();
            apply_plan(context, &mlil, func, &snap, &types, &plan, &targets)?
        };
        stats.apply_build += times.build;
        stats.apply_finalize += times.finalize;
        stats.apply_ssa += times.ssa;
        stats.apply_commit += times.commit;
        stats.apply_retype += times.retype;
        stats.apply += clock.lap();
        if count == 0 {
            break;
        }
        total += count;
        stats.outlined = total;
        let mut names: Vec<&str> = used.iter().filter(|p| has_target[**p]).map(|p| patterns[*p].name.as_str()).collect();
        names.sort();
        names.dedup();
        summary.push(format!("round {}: {found} -> {} region(s): {}", round_no + 1, count, names.join(", ")));
    }
    stats.summary = summary;
    // The manager tests patterns against the code as it was before outlining.
    match (total, original) {
        (n, Some(first)) if n > 0 => store::remember_original(view, func.start(), first),
        _ => store::forget_original(view, func.start()),
    }
    if total > 0 {
        if let Some(mlil) = unsafe { Mlil::owned(BNAnalysisContextGetMediumLevelILFunction(context)) } {
            record_references(context, &mlil, &func.arch_name(), &store::target_addresses(view));
        }
    }
    stats.finish = clock.lap();
    Ok(())
}

pub fn register_settings() {
    unsafe {
        let settings = BNCreateSettings(cstr("default").as_ptr());
        if settings.is_null() {
            return;
        }
        BNSettingsRegisterGroup(settings, cstr("outliner").as_ptr(), cstr("Outliner").as_ptr());
        BNSettingsRegisterSetting(settings, cstr(SETTING_RETYPE).as_ptr(), cstr(SETTING_RETYPE_PROPERTIES).as_ptr());
        BNFreeSettings(settings);
    }
}

/// Clones the function workflow with the outlining activity inserted before
/// HLIL generation and registers it.
pub fn register() -> Result<(), String> {
    register_settings();
    unsafe {
        let base = BNWorkflowGet(cstr(BASE_WORKFLOW).as_ptr());
        if base.is_null() {
            return Err(format!("workflow {BASE_WORKFLOW} not found"));
        }
        let empty = cstr("");
        let workflow = BNWorkflowClone(base, empty.as_ptr(), empty.as_ptr());
        BNFreeWorkflow(base);
        if workflow.is_null() {
            return Err("could not clone the function workflow".to_string());
        }
        let activity = BNCreateActivity(cstr(ACTIVITY_CONFIG).as_ptr(), std::ptr::null_mut(), Some(outline_action));
        if activity.is_null() {
            BNFreeWorkflow(workflow);
            return Err("could not create the outliner activity".to_string());
        }
        let registered = BNWorkflowRegisterActivity(workflow, activity, std::ptr::null_mut(), 0);
        BNFreeActivity(activity);
        if registered.is_null() {
            BNFreeWorkflow(workflow);
            return Err("failed to register outliner activity".to_string());
        }
        BNFreeActivity(registered);
        let name = cstr(ACTIVITY_NAME);
        let mut names = [name.as_ptr()];
        let inserted = BNWorkflowInsert(workflow, cstr(ANCHOR_ACTIVITY).as_ptr(), names.as_mut_ptr(), 1)
            || BNWorkflowInsertAfter(workflow, cstr(FALLBACK_ANCHOR).as_ptr(), names.as_mut_ptr(), 1);
        if !inserted {
            BNFreeWorkflow(workflow);
            return Err("failed to insert outliner activity into the function workflow".to_string());
        }
        let ok = BNRegisterWorkflow(workflow, empty.as_ptr());
        BNFreeWorkflow(workflow);
        if !ok {
            return Err("failed to register modified function workflow".to_string());
        }
    }
    log_info(&format!("registered activity {ACTIVITY_NAME} in {BASE_WORKFLOW}"));
    Ok(())
}
