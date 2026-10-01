//! Running the matchers over a function outside the workflow: what the
//! manager's preview, the failure explanations and the drafters need.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use outliner_core::draft::{draft_function, draft_region, Draft};
use outliner_core::fused::find_fused_matches;
use outliner_core::generalize::{generalize, Generalized};
use outliner_core::matcher::{arg_var_set, explain_pattern, find_matches, Round};
use outliner_core::pattern::{parse_pattern, Pattern, Rule};
use outliner_core::plan::build_plan;
use outliner_core::render::render_stmt;
use outliner_core::sites::find_expression_sites;
use serde::Serialize;

use crate::env::BnEnv;
use crate::ffi::{var_identifier, Func, Mlil, View};
use crate::rewrite::{build_rewrite, Target};
use crate::snapshot::{self, Snapshot, VarOverrides};
use crate::store;
use crate::types::TypeTable;

/// A function's current MLIL, snapshotted, with an environment for it.
struct Loaded {
    snap: Snapshot,
    env: BnEnv,
}

fn load(view: &View, func: &Func) -> Option<Loaded> {
    let mlil = func.mlil()?;
    let env = BnEnv::new(view.clone(), func, TypeTable::default());
    env.begin_round(mlil.clone());
    let snap = {
        let mut types = env.types.borrow_mut();
        snapshot::read(&mlil, func, &mut types)
    };
    Some(Loaded { snap, env })
}

fn symbols_of(view: &View) -> impl Fn(u64) -> Vec<String> + '_ {
    move |addr: u64| {
        let mut names: Vec<String> = view.symbols_at(addr).iter().map(|s| s.raw_name()).collect();
        if let Some(f) = view.function_at(addr) {
            names.push(f.name());
        }
        names.sort();
        names.dedup();
        names
    }
}

// --------------------------------------------------------------------------- drafting

#[derive(Serialize)]
pub struct DraftReport {
    pub ok: bool,
    /// True for a request the manager resolves itself (it can read the
    /// selected instructions from the view); `function`, `start` and `end`
    /// then say where the selection is.
    pub request: bool,
    pub text: String,
    pub notes: Vec<String>,
    pub function: u64,
    pub name: String,
    pub start: u64,
    pub end: u64,
    pub error: String,
}

impl DraftReport {
    fn failure(error: String) -> DraftReport {
        DraftReport { ok: false, request: false, text: String::new(), notes: Vec::new(), function: 0, name: String::new(), start: 0, end: 0, error }
    }

    fn from(draft: Draft, func: &Func, start: u64, end: u64) -> DraftReport {
        DraftReport { ok: true, request: false, text: draft.text, notes: draft.notes, function: func.start(), name: func.name(), start, end, error: String::new() }
    }

    /// A request to draft the selection `[start, end)` of the function holding it.
    pub fn request(view: &View, start: u64, end: u64) -> DraftReport {
        match view.function_containing(start) {
            Some(func) => DraftReport { ok: true, request: true, text: String::new(), notes: Vec::new(), function: func.start(), name: func.name(), start, end, error: String::new() },
            None => DraftReport::failure(format!("no function holds {start:#x}")),
        }
    }
}

/// Drafts a pattern for the instructions in the address range `[start, end)`
/// of the function holding it (an empty range means the instruction at `start`).
/// Blocks of the function may be laid out out of address order, so a range
/// can take in lines the user did not select; the manager prefers
/// [`draft_indices`] when the view tells it the selected instructions.
pub fn draft_selection(view: &View, start: u64, end: u64) -> DraftReport {
    let Some(func) = view.function_containing(start) else {
        return DraftReport::failure(format!("no function holds {start:#x}"));
    };
    let Some(loaded) = load(view, &func) else {
        return DraftReport::failure(format!("{} has no MLIL yet", func.name()));
    };
    let f = &loaded.snap.f;
    let end = if end > start { end } else { start + 1 };
    let region: Vec<u32> = (0..f.len() as u32).filter(|i| (start..end).contains(&f.expr(f.instr(*i)).address)).collect();
    if region.is_empty() {
        return DraftReport::failure(format!("no MLIL instruction of {} lies in {start:#x}-{end:#x}", func.name()));
    }
    draft_instructions(view, &func, &loaded, &region, start, end)
}

/// Drafts a pattern for MLIL instructions `first..=last` of the function at `func`.
pub fn draft_indices(view: &View, func: u64, first: u32, last: u32) -> DraftReport {
    let Some(func) = view.function_at(func).or_else(|| view.function_containing(func)) else {
        return DraftReport::failure(format!("no function at {func:#x}"));
    };
    let Some(loaded) = load(view, &func) else {
        return DraftReport::failure(format!("{} has no MLIL yet", func.name()));
    };
    let f = &loaded.snap.f;
    let (first, last) = (first.min(last), first.max(last));
    if last as usize >= f.len() {
        return DraftReport::failure(format!("{} has {} MLIL instructions, not {}", func.name(), f.len(), last + 1));
    }
    let region: Vec<u32> = (first..=last).collect();
    let addresses = region.iter().map(|i| f.expr(f.instr(*i)).address);
    let start = addresses.clone().min().unwrap_or(0);
    let end = addresses.max().map(|a| a + 1).unwrap_or(start);
    draft_instructions(view, &func, &loaded, &region, start, end)
}

fn draft_instructions(view: &View, func: &Func, loaded: &Loaded, region: &[u32], start: u64, end: u64) -> DraftReport {
    let symbols = symbols_of(view);
    match draft_region(&loaded.snap.f, &loaded.env, Some(&symbols), region, "outlined") {
        Ok(draft) => DraftReport::from(draft, func, start, end),
        Err(e) => DraftReport::failure(e),
    }
}

/// Drafts a pattern from a whole function: its out-of-line body.
pub fn draft_whole_function(view: &View, addr: u64) -> DraftReport {
    let Some(func) = view.function_at(addr).or_else(|| view.function_containing(addr)) else {
        return DraftReport::failure(format!("no function at {addr:#x}"));
    };
    let Some(loaded) = load(view, &func) else {
        return DraftReport::failure(format!("{} has no MLIL yet", func.name()));
    };
    let params: Vec<_> = func.parameter_vars().iter().filter_map(|v| loaded.snap.var_ids.get(&var_identifier(v)).copied()).collect();
    let name = func.name();
    let ty = func.ty();
    let signature = ty.as_ref().map_or(format!("int64_t {name}()"), |t| t.declaration(&name));
    let returns = ty.and_then(|t| t.child()).is_some_and(|r| r.class() != binaryninjacore_sys::BNTypeClass::VoidTypeClass);
    let symbols = symbols_of(view);
    match draft_function(&loaded.snap.f, &loaded.env, Some(&symbols), &params, &signature, returns) {
        Ok(draft) => DraftReport::from(draft, &func, func.start(), func.start()),
        Err(e) => DraftReport::failure(e),
    }
}

// --------------------------------------------------------------------------- preview

#[derive(Serialize, Clone)]
pub struct Hit {
    pub function: String,
    pub address: u64,
    pub kind: String,
    pub round: usize,
    pub instr: u32,
    pub text: String,
}

#[derive(Serialize, Clone)]
pub struct Diagnosis {
    pub function: String,
    /// The function's start.
    pub address: u64,
    pub line: Option<u32>,
    pub matched: u32,
    pub instr: u32,
    pub code: String,
    pub reason: String,
}

#[derive(Serialize, Clone)]
pub struct PatternReport {
    pub title: String,
    /// The text's position in the list tested.
    pub index: usize,
    /// The function the pattern describes (a rules chunk's name; empty when
    /// the text does not compile).
    pub name: String,
    pub error: String,
    pub hits: Vec<Hit>,
    /// Why the pattern does not match each focus function it misses.
    pub diagnoses: Vec<Diagnosis>,
}

#[derive(Serialize, Clone)]
pub struct Preview {
    /// One report per text, or per reported text when some were chosen.
    pub patterns: Vec<PatternReport>,
    /// Functions tested.
    pub functions: usize,
    /// Functions skipped for having no MLIL yet.
    pub skipped: usize,
    pub cancelled: bool,
    /// Why nothing was tested (the chosen tab holds rewrite rules).
    pub message: String,
    /// Focus functions that no reported pattern matched.
    pub uncovered: Vec<FunctionRef>,
    /// Titles of the other tabs left out because they do not compile.
    pub left_out: Vec<String>,
}

impl Preview {
    fn empty() -> Self {
        Preview { patterns: Vec::new(), functions: 0, skipped: 0, cancelled: false, message: String::new(), uncovered: Vec::new(), left_out: Vec::new() }
    }
}

/// A function, by name and start.
#[derive(Serialize, Clone)]
pub struct FunctionRef {
    pub name: String,
    pub address: u64,
}

/// A stand-in address for a pattern that has no registered call target yet,
/// so that a preview can build the calls later rounds match against.
fn stand_in_address(k: usize) -> u64 {
    u64::MAX - 0x1_0000 + 16 * k as u64
}

/// The MLIL a function is tested with: the one the activity found it with,
/// when it outlined something there, else its current one (never generated
/// on the spot: a function without MLIL is skipped).
fn original_or_current(view: &View, func: &Func) -> Option<Mlil> {
    store::original_mlil(view, func.start()).or_else(|| func.mlil_if_available())
}

/// The compiled patterns of a test, shared by the worker threads.
struct Setup {
    patterns: Vec<Pattern>,
    rules: Vec<Rule>,
    targets: Vec<Option<Target>>,
    has_target: Vec<bool>,
    /// Stand-in call targets by address, with the name the pattern calls them.
    stand_ins: Vec<(u64, String)>,
    /// Report slot by compiled pattern index.
    slots: Vec<usize>,
    /// Reports in tab order: compile errors are known up front.
    reports: Vec<PatternReport>,
    /// The texts whose patterns are tested and reported, in order; the others
    /// only take part, the way the workflow would run them.  None: all.
    report: Option<Vec<usize>>,
    /// Which tabs hold rewrite rules.
    rules_tabs: Vec<bool>,
}

impl Setup {
    /// Whether the compiled pattern `pattern` is reported.
    fn reported(&self, pattern: usize) -> bool {
        self.report.as_ref().is_none_or(|tabs| tabs.contains(&self.slots[pattern]))
    }
}

fn setup(view: &View, texts: &[String], report: Option<Vec<usize>>) -> Setup {
    let report = report.map(|tabs| {
        let mut kept: Vec<usize> = Vec::new();
        for tab in tabs {
            if tab < texts.len() && !kept.contains(&tab) {
                kept.push(tab);
            }
        }
        kept
    });
    let mut setup = Setup {
        patterns: Vec::new(),
        rules: Vec::new(),
        targets: Vec::new(),
        has_target: Vec::new(),
        stand_ins: Vec::new(),
        slots: Vec::new(),
        reports: Vec::new(),
        report,
        rules_tabs: Vec::new(),
    };
    for (index, text) in texts.iter().enumerate() {
        let title = outliner_core::pattern::chunk_title(text);
        match store::compile_text(view, text) {
            Ok(mut p) => {
                setup.rules.append(&mut p.rules);
                let is_rules = p.is_rules();
                setup.reports.push(PatternReport { title, index, name: p.name.clone(), error: String::new(), hits: Vec::new(), diagnoses: Vec::new() });
                setup.rules_tabs.push(is_rules);
                if is_rules {
                    continue;
                }
                setup.slots.push(setup.reports.len() - 1);
                // The registered target, else a stand-in with the signature's type and name.
                let target = match store::resolve_target(view, &p) {
                    Some((addr, ty)) => Some(Target { addr, ty }),
                    None => p.signature.as_deref().and_then(|sig| store::parse_signature(view, sig).ok()).map(|sig| {
                        let addr = stand_in_address(setup.stand_ins.len());
                        setup.stand_ins.push((addr, sig.name.clone()));
                        Target { addr, ty: sig.ty.clone() }
                    }),
                };
                setup.targets.push(target);
                setup.patterns.push(p);
            }
            Err(e) => {
                setup.reports.push(PatternReport { title, index, name: String::new(), error: e, hits: Vec::new(), diagnoses: Vec::new() });
                setup.rules_tabs.push(false);
            }
        }
    }
    setup.has_target = setup.targets.iter().map(Option::is_some).collect();
    setup
}

/// What one function contributes: hits by report slot, and diagnoses when
/// it is the focus function.
#[derive(Default)]
struct Found {
    hits: Vec<(usize, Hit)>,
    diagnoses: Vec<(usize, Diagnosis)>,
    /// For a focus function: it, and whether a reported pattern matched there.
    focus: Option<(FunctionRef, bool)>,
}

/// Tests the patterns on one function the way the workflow would run them:
/// on the code as it was before outlining, round after round, each round's
/// rewrite built in a scratch copy.  None when the function has no MLIL.
fn preview_function(view: &View, func: &Func, setup: &Setup, explain: bool) -> Option<Found> {
    let mut mlil = original_or_current(view, func)?;
    let name = func.name();
    let env = BnEnv::new(view.clone(), func, TypeTable::default());
    for (addr, target_name) in &setup.stand_ins {
        env.name_address(*addr, target_name);
    }
    let patterns = &setup.patterns;
    let rules = &setup.rules;
    let mut found = Found::default();
    let mut overrides: VarOverrides = HashMap::new();
    // The states explanations are tried on: the code before outlining and
    // after the last round, each with the MLIL its queries are answered from.
    let mut first_state: Option<(Snapshot, Mlil)> = None;
    let mut last_state: Option<(Snapshot, Mlil)> = None;
    let mut matched: HashSet<usize> = HashSet::new();
    for round in 1..=crate::workflow::MAX_ROUNDS {
        env.begin_round(mlil.clone());
        let snap = {
            let mut types = env.types.borrow_mut();
            snapshot::read_with(&mlil, func, &mut types, &overrides)
        };
        let f = &snap.f;
        let (matches, fused, sites) = {
            let round_state = Round::new(f, &env);
            let matches = find_matches(&round_state, patterns, rules, None);
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
            let fused = find_fused_matches(&round_state, patterns, rules, Some(&claimed), &deleted, &live);
            for fm in &fused {
                for start in &fm.blocks_touched {
                    if let Some(b) = f.block_at(*start) {
                        claimed.insert(b.id.0 as usize);
                    }
                }
                deleted.union_with(&fm.deleted);
                for call in &fm.calls {
                    for id in patterns[call.pattern].param_ids().into_iter().flatten() {
                        if let Some(b) = call.binding(id) {
                            for v in b.reads(f) {
                                live.insert(v.0 as usize);
                            }
                        }
                    }
                }
            }
            let sites = find_expression_sites(&round_state, patterns, rules, Some(&claimed), &deleted, &live);
            (matches, fused, sites)
        };
        let mut hit = |pattern: usize, kind: &str, instr: u32| {
            matched.insert(pattern);
            if !setup.reported(pattern) {
                return;
            }
            found.hits.push((
                setup.slots[pattern],
                Hit { function: name.clone(), address: f.expr(f.instr(instr)).address, kind: kind.to_string(), round, instr, text: render_stmt(f, instr, None) },
            ));
        };
        for m in &matches {
            hit(m.pattern, "plain", m.entry_index);
        }
        for fm in &fused {
            for c in &fm.calls {
                hit(c.pattern, "fused", fm.guard_index);
            }
        }
        for s in &sites {
            hit(s.pattern, "expression", s.instr_index);
        }
        let nothing = matches.is_empty() && fused.is_empty() && sites.is_empty();
        let plan = if nothing { None } else { build_plan(f, patterns, &matches, &fused, &sites, &setup.has_target, true).ok() };
        let built = match plan.filter(|p| !p.is_empty()) {
            Some(plan) => {
                let types = env.types.borrow();
                build_rewrite(&mlil, func, &snap, &types, &plan, &setup.targets, false).ok()
            }
            None => None,
        };
        if first_state.is_none() {
            first_state = Some((snap, mlil.clone()));
        } else {
            last_state = Some((snap, mlil.clone()));
        }
        let Some(built) = built else { break };
        for fresh in &built.fresh {
            overrides.insert(var_identifier(&fresh.var), (fresh.name.clone(), fresh.ty.clone()));
        }
        for (var, ty, var_name) in &built.retype {
            overrides.insert(var_identifier(var), (var_name.clone(), Some(ty.clone())));
        }
        mlil = built.mlil;
    }
    if !explain {
        return Some(found);
    }
    let covered = matched.iter().any(|pi| setup.reported(*pi));
    found.focus = Some((FunctionRef { name: name.clone(), address: func.start() }, covered));
    // Explain what stopped the patterns that never matched here, on the code
    // before outlining and after the last round, whichever got further.
    let Some(first) = first_state else { return Some(found) };
    let states: Vec<&(Snapshot, Mlil)> = std::iter::once(&first).chain(last_state.iter()).collect();
    for (pi, pattern) in patterns.iter().enumerate() {
        if matched.contains(&pi) || pattern.value.is_some() || !setup.reported(pi) {
            continue;
        }
        // Another shape of the same function matched here: this one's miss is expected.
        if patterns.iter().enumerate().any(|(q, other)| q != pi && matched.contains(&q) && setup.reported(q) && other.name == pattern.name) {
            continue;
        }
        let mut best: Option<Diagnosis> = None;
        for (state, state_mlil) in &states {
            let f = &state.f;
            env.begin_round(state_mlil.clone());
            let round_state = Round::new(f, &env);
            if let Err(e) = explain_pattern(&round_state, patterns, pi, rules, None) {
                let code = if (e.attempt.instr as usize) < f.len() { render_stmt(f, e.attempt.instr, None) } else { String::new() };
                let d = Diagnosis {
                    function: name.clone(),
                    address: func.start(),
                    line: e.line(pattern),
                    matched: e.attempt.matched,
                    instr: e.attempt.instr,
                    code,
                    reason: e.attempt.reason.clone().unwrap_or_else(|| "no statement of the pattern matches".to_string()),
                };
                if best.as_ref().is_none_or(|b| d.matched > b.matched) {
                    best = Some(d);
                }
            }
        }
        if let Some(d) = best {
            found.diagnoses.push((setup.slots[pi], d));
        }
    }
    Some(found)
}

/// A test running in the background: progress the dialog polls, a cancel
/// flag it sets, and the result once the workers are done.
pub struct PreviewJob {
    pub total: AtomicUsize,
    pub processed: AtomicUsize,
    pub cancel: AtomicBool,
    pub done: AtomicBool,
    result: Mutex<Option<Preview>>,
}

impl PreviewJob {
    /// The result, once there is one.
    pub fn take_result(&self) -> Option<Preview> {
        self.result.lock().unwrap_or_else(|e| e.into_inner()).take()
    }
}

static JOBS: Mutex<Vec<(u64, Arc<PreviewJob>)>> = Mutex::new(Vec::new());
static NEXT_JOB: AtomicUsize = AtomicUsize::new(1);

pub fn job(id: u64) -> Option<Arc<PreviewJob>> {
    JOBS.lock().unwrap_or_else(|e| e.into_inner()).iter().find(|(k, _)| *k == id).map(|(_, j)| j.clone())
}

pub fn forget_job(id: u64) {
    JOBS.lock().unwrap_or_else(|e| e.into_inner()).retain(|(k, _)| *k != id);
}

/// Starts a test of the pattern texts over every function of the view on a
/// thread of its own (the functions spread over as many workers as the
/// machine has cores); `focus` holds function starts where each reported
/// pattern that does not match gets explained.  With `report`, only the
/// patterns of those texts are tested and reported: the other texts still
/// run, since a pattern may match only code another one outlined, but what
/// they match is not collected.  Returns the job's id.
pub fn start_preview(view: &View, texts: Vec<String>, focus: Vec<u64>, report: Option<Vec<usize>>) -> u64 {
    let id = NEXT_JOB.fetch_add(1, Ordering::Relaxed) as u64;
    let job = Arc::new(PreviewJob { total: AtomicUsize::new(0), processed: AtomicUsize::new(0), cancel: AtomicBool::new(false), done: AtomicBool::new(false), result: Mutex::new(None) });
    {
        // A finished job whose result was never fetched (a dialog closed
        // mid-test) is of no use to anyone.
        let mut jobs = JOBS.lock().unwrap_or_else(|e| e.into_inner());
        jobs.retain(|(_, j)| !j.done.load(Ordering::SeqCst));
        jobs.push((id, job.clone()));
    }
    let view = view.clone();
    std::thread::spawn(move || {
        let setup = setup(&view, &texts, report);
        let mut message = String::new();
        let mut left_out = Vec::new();
        let mut functions = view.functions();
        if let Some(tabs) = &setup.report {
            // Nothing to scan for when no reported text is a pattern that compiles.
            if !tabs.iter().any(|t| !setup.rules_tabs[*t] && setup.reports[*t].error.is_empty()) {
                if !tabs.is_empty() && tabs.iter().all(|t| setup.rules_tabs[*t]) {
                    message = "Rewrite rules have no matches of their own; every test uses them. Test a pattern to see them at work.".to_string();
                }
                functions.clear();
            }
            left_out = setup.reports.iter().enumerate().filter(|(k, r)| !tabs.contains(k) && !r.error.is_empty()).map(|(_, r)| r.title.clone()).collect();
        }
        let focus: HashSet<u64> = focus.into_iter().collect();
        job.total.store(functions.len(), Ordering::Relaxed);
        let workers = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4).clamp(1, 32);
        let next = AtomicUsize::new(0);
        let skipped = AtomicUsize::new(0);
        let collected: Mutex<Vec<Found>> = Mutex::new(Vec::new());
        std::thread::scope(|scope| {
            for _ in 0..workers {
                scope.spawn(|| {
                    let mut mine: Vec<Found> = Vec::new();
                    loop {
                        if job.cancel.load(Ordering::Relaxed) {
                            break;
                        }
                        let k = next.fetch_add(1, Ordering::Relaxed);
                        let Some(func) = functions.get(k) else { break };
                        let explain = focus.contains(&func.start());
                        match preview_function(&view, func, &setup, explain) {
                            Some(found) if found.hits.is_empty() && found.diagnoses.is_empty() && found.focus.is_none() => {}
                            Some(found) => mine.push(found),
                            None => {
                                skipped.fetch_add(1, Ordering::Relaxed);
                            }
                        }
                        job.processed.fetch_add(1, Ordering::Relaxed);
                    }
                    collected.lock().unwrap_or_else(|e| e.into_inner()).append(&mut mine);
                });
            }
        });
        let mut reports = setup.reports;
        let mut uncovered: Vec<FunctionRef> = Vec::new();
        for found in collected.into_inner().unwrap_or_else(|e| e.into_inner()) {
            if let Some((function, false)) = found.focus {
                uncovered.push(function);
            }
            for (slot, hit) in found.hits {
                reports[slot].hits.push(hit);
            }
            for (slot, d) in found.diagnoses {
                reports[slot].diagnoses.push(d);
            }
        }
        for r in &mut reports {
            r.hits.sort_by_key(|h| (h.address, h.round, h.instr));
            r.diagnoses.sort_by_key(|d| d.address);
        }
        if let Some(tabs) = &setup.report {
            reports = tabs.iter().map(|t| reports[*t].clone()).collect();
        }
        uncovered.sort_by_key(|f| f.address);
        let cancelled = job.cancel.load(Ordering::Relaxed);
        let preview =
            Preview { patterns: reports, functions: job.processed.load(Ordering::Relaxed), skipped: skipped.into_inner(), cancelled, message, uncovered, left_out };
        *job.result.lock().unwrap_or_else(|e| e.into_inner()) = Some(preview);
        job.done.store(true, Ordering::SeqCst);
    });
    id
}

/// Runs a test to completion on the calling thread (for scripts).
pub fn preview(view: &View, texts: &[String], focus: Vec<u64>, report: Option<Vec<usize>>) -> Preview {
    let id = start_preview(view, texts.to_vec(), focus, report);
    let job = job(id).expect("the job was just registered");
    while !job.done.load(Ordering::SeqCst) {
        std::thread::sleep(std::time::Duration::from_millis(20));
    }
    forget_job(id);
    job.take_result().unwrap_or_else(Preview::empty)
}

// --------------------------------------------------------------------------- generalising

#[derive(Serialize)]
pub struct Merge {
    pub kind: String,
    pub text: String,
    pub notes: Vec<String>,
    pub error: String,
}

/// Generalises the pattern `base` with a second instance drafted as `other`.
pub fn merge(base: &str, other: &str) -> Merge {
    let failure = |e: String| Merge { kind: "error".into(), text: String::new(), notes: Vec::new(), error: e };
    let base = match parse_pattern(base) {
        Ok(p) => p,
        Err(e) => return failure(format!("the pattern being extended does not parse: {e}")),
    };
    let other = match parse_pattern(other) {
        Ok(p) => p,
        Err(e) => return failure(format!("the second instance does not parse: {e}")),
    };
    match generalize(&base, &other) {
        Generalized::Merged { text, notes } => Merge { kind: "merged".into(), text, notes, error: String::new() },
        Generalized::Chunk { text, why } => Merge { kind: "chunk".into(), text, notes: vec![why], error: String::new() },
    }
}
