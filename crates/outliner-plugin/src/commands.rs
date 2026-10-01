//! Plugin commands: the pattern manager, rendering a function in pattern
//! syntax, and the timing report used by scripts.
//!
//! The manager is a Qt dialog, which the core's C API cannot build, so the
//! plugin runs it inside Binary Ninja's Python (`manager.py`, embedded here);
//! the dialog reads, validates and saves patterns through the plugin's C API,
//! so the plugin's own store and caches stay the single source of truth.

use std::os::raw::c_void;
use std::sync::Mutex;

use binaryninjacore_sys::*;
use outliner_core::render::render_function;

use crate::ffi::{cstr, log_error, plugin_path, user_directory, Func, View};
use crate::snapshot;
use crate::types::TypeTable;
use crate::workflow;

/// The text a new pattern starts from.
pub const TEMPLATE: &str = "signature: char const* my_accessor(`std::__1::string` const* s) __pure
$s : /string/

# Describe the MLIL to outline below.  Plugins > Outliner > Show Function As
# Pattern Text prints any function in this syntax.  Assign the result to $ret,
# or replace the statements with \"value: <expr>\" to outline an expression
# wherever it occurs.
$ret = load_struct.q($s, 0)
";

const MANAGER_SCRIPT: &str = include_str!("../manager.py");
const MANAGER_FILE: &str = "outliner_manager.py";

fn report(view: &View, title: &str, text: &str) {
    unsafe { BNShowPlainTextReport(view.raw(), cstr(title).as_ptr(), cstr(text).as_ptr()) }
}

// --------------------------------------------------------------------------- pattern text

/// The function's signature (with C++ names escaped for the type parser) and
/// its MLIL rendered in pattern syntax.
pub fn function_pattern_text(view: &View, func: &Func) -> String {
    let name = func.name();
    let mut header = vec![
        format!("# {name} @ {:#x}", func.start()),
        "# signature (escaped for the type parser):".to_string(),
        format!("#   {}", func.ty().map_or(name.clone(), |t| t.declaration(&name))),
        "# parameters:".to_string(),
    ];
    for var in func.parameter_vars() {
        let var_name = func.var_name(&var);
        let declaration = func.var_type(&var).map_or(var_name.clone(), |t| t.declaration(&var_name));
        header.push(format!("#   {declaration}    -> ${var_name}"));
    }
    header.push("# Copy the lines of the inlined code below, rename the parameter placeholders to the".to_string());
    header.push("# names in your signature, rename the result variable to $ret, and drop the rest.".to_string());
    header.push(String::new());
    let Some(mlil) = func.mlil() else {
        return format!("{}# (no MLIL available)\n", header.join("\n"));
    };
    let mut types = TypeTable::default();
    let snap = snapshot::read(&mlil, func, &mut types);
    let symbols = |addr: u64| -> Vec<String> {
        let mut names: Vec<String> = view.symbols_at(addr).iter().map(|s| s.raw_name()).collect();
        if let Some(f) = view.function_at(addr) {
            names.push(f.name());
        }
        names.sort();
        names.dedup();
        names
    };
    format!("{}\n{}", header.join("\n"), render_function(&snap.f, Some(&symbols), None, None))
}

// --------------------------------------------------------------------------- the manager

/// The Python scripting instance the manager runs in, created on first use.
struct Python(*mut BNScriptingInstance);

unsafe impl Send for Python {}

static PYTHON: Mutex<Option<Python>> = Mutex::new(None);

fn python_instance() -> Result<*mut BNScriptingInstance, String> {
    let mut slot = PYTHON.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(instance) = slot.as_ref() {
        return Ok(instance.0);
    }
    unsafe {
        let provider = BNGetScriptingProviderByName(cstr("Python").as_ptr());
        if provider.is_null() {
            return Err("Binary Ninja's Python scripting support is not available".to_string());
        }
        let instance = BNCreateScriptingProviderInstance(provider);
        if instance.is_null() {
            return Err("could not create a Python scripting instance".to_string());
        }
        *slot = Some(Python(instance));
        Ok(instance)
    }
}

/// Writes the manager script next to the plugin library (or into the user
/// directory when that folder is not writable) and returns its path.  `draft`
/// is the JSON of a pattern drafted from code, opened as a new tab.
fn write_manager_script(plugin: &str, view: &View, draft: &str) -> Result<String, String> {
    let function = view.function_containing(view.current_offset()).map(|f| f.start()).unwrap_or(0);
    let script = MANAGER_SCRIPT
        .replace("@@PLUGIN@@", &plugin.replace('\\', "\\\\").replace('"', "\\\""))
        .replace("@@VIEW@@", &format!("{:#x}", view.raw() as usize))
        .replace("@@FUNCTION@@", &format!("{function:#x}"))
        .replace("@@DRAFT@@", draft);
    let folder = std::path::Path::new(plugin).parent().map(|p| p.to_string_lossy().into_owned()).unwrap_or_default();
    let mut errors = Vec::new();
    for dir in [folder, user_directory()] {
        let path = format!("{dir}/{MANAGER_FILE}");
        match std::fs::write(&path, &script) {
            Ok(()) => return Ok(path),
            Err(e) => errors.push(format!("{path}: {e}")),
        }
    }
    Err(format!("could not write the manager script ({})", errors.join("; ")))
}

/// Opens the pattern manager for `view`, with a drafted pattern when given.
fn show_manager(view: &View, draft: Option<&crate::analysis::DraftReport>) -> Result<(), String> {
    let plugin = plugin_path().ok_or("could not determine the plugin's own path")?;
    // The draft goes into a Python string literal that json.loads reads.
    let draft = match draft {
        Some(d) => serde_json::to_string(d).map_err(|e| e.to_string())?,
        None => "null".to_string(),
    };
    let draft = draft.replace('\\', "\\\\").replace('"', "\\\"");
    let path = write_manager_script(&plugin, view, &draft)?;
    let instance = python_instance()?;
    unsafe {
        BNSetScriptingInstanceCurrentBinaryView(instance, view.raw());
        match BNExecuteScriptInputFromFilename(instance, cstr(&path).as_ptr()) {
            BNScriptingProviderExecuteResult::SuccessfulScriptExecution => Ok(()),
            other => Err(format!("the manager script was not accepted ({other:?})")),
        }
    }
}

fn report_error(message: &str) {
    log_error(message);
    unsafe {
        BNShowMessageBox(cstr("Outliner").as_ptr(), cstr(message).as_ptr(), BNMessageBoxButtonSet::OKButtonSet, BNMessageBoxIcon::ErrorIcon);
    }
}

fn cmd_manage(view: &View) {
    if let Err(e) = show_manager(view, None) {
        report_error(&format!("Outliner could not open the pattern manager: {e}"));
    }
}

/// Opens the manager on a draft, or says why there is none.
fn open_draft(view: &View, draft: crate::analysis::DraftReport) {
    if !draft.ok {
        return report_error(&format!("Outliner could not draft a pattern: {}", draft.error));
    }
    if let Err(e) = show_manager(view, Some(&draft)) {
        report_error(&format!("Outliner could not open the pattern manager: {e}"));
    }
}

fn cmd_draft_selection(view: &View, start: u64, len: u64) {
    // The manager resolves the selection: the view can tell it the selected
    // instructions, which an address range cannot when blocks are laid out
    // out of address order.
    open_draft(view, crate::analysis::DraftReport::request(view, start, start.saturating_add(len)));
}

fn cmd_draft_function(view: &View, func: &Func) {
    open_draft(view, crate::analysis::draft_whole_function(view, func.start()));
}

fn cmd_show(view: &View, func: &Func) {
    report(view, &format!("Pattern text for {}", func.name()), &function_pattern_text(view, func));
}

// --------------------------------------------------------------------------- timing

/// The timing report: per-phase totals over every activity invocation since
/// the last reset.
pub fn timing_report(stats: &[workflow::Stats]) -> String {
    let n = stats.len();
    let sum = |f: &dyn Fn(&workflow::Stats) -> f64| stats.iter().map(f).sum::<f64>();
    let count = |f: &dyn Fn(&workflow::Stats) -> usize| stats.iter().map(f).sum::<usize>();
    let mut lines = vec![
        format!("{n} activity invocation(s), {} instruction(s), {} round(s), {} region(s) outlined", count(&|s| s.instructions), count(&|s| s.rounds), count(&|s| s.outlined)),
        format!("pattern compilations: {}", crate::store::COMPILES.load(std::sync::atomic::Ordering::Relaxed)),
        String::new(),
        format!("{:<16}{:>10}", "phase", "seconds"),
    ];
    type Phase<'a> = (&'a str, &'a dyn Fn(&workflow::Stats) -> f64);
    let phases: [Phase; 13] = [
        ("patterns", &|s| s.patterns),
        ("setup", &|s| s.setup),
        ("view", &|s| s.view),
        ("plain", &|s| s.plain),
        ("fused", &|s| s.fused),
        ("sites", &|s| s.sites),
        ("apply", &|s| s.apply),
        ("  build", &|s| s.apply_build),
        ("  finalize", &|s| s.apply_finalize),
        ("  ssa", &|s| s.apply_ssa),
        ("  commit", &|s| s.apply_commit),
        ("  retype", &|s| s.apply_retype),
        ("finish", &|s| s.finish),
    ];
    for (name, f) in phases {
        lines.push(format!("{name:<16}{:>10.3}", sum(f)));
    }
    lines.push(format!("{:<16}{:>10.3}", "total", sum(&|s| s.total)));
    lines.push(String::new());
    let mut slowest: Vec<&workflow::Stats> = stats.iter().collect();
    slowest.sort_by(|a, b| b.total.partial_cmp(&a.total).unwrap_or(std::cmp::Ordering::Equal));
    lines.push("slowest functions:".to_string());
    for s in slowest.iter().take(10) {
        lines.push(format!("  {:>8.3} s  {} ({} instr, {} round(s), {} outlined)", s.total, s.function, s.instructions, s.rounds, s.outlined));
    }
    lines.join("\n") + "\n"
}

// --------------------------------------------------------------------------- registration

type ViewCommand = fn(&View);
type FunctionCommand = fn(&View, &Func);
type RangeCommand = fn(&View, u64, u64);

unsafe extern "C" fn range_action(ctxt: *mut c_void, view: *mut BNBinaryView, addr: u64, len: u64) {
    let command: RangeCommand = std::mem::transmute(ctxt);
    if let Some(view) = View::borrowed(view) {
        command(&view, addr, len);
    }
}

unsafe extern "C" fn view_action(ctxt: *mut c_void, view: *mut BNBinaryView) {
    let command: ViewCommand = std::mem::transmute(ctxt);
    if let Some(view) = View::borrowed(view) {
        command(&view);
    }
}

unsafe extern "C" fn function_action(ctxt: *mut c_void, view: *mut BNBinaryView, func: *mut BNFunction) {
    let command: FunctionCommand = std::mem::transmute(ctxt);
    if let (Some(view), Some(func)) = (View::borrowed(view), Func::borrowed(func)) {
        command(&view, &func);
    }
}

pub fn register() {
    unsafe {
        BNRegisterPluginCommand(
            cstr("Outliner\\Manage Patterns...").as_ptr(),
            cstr("Add, edit and remove the MLIL patterns outlined into calls").as_ptr(),
            Some(view_action),
            None,
            cmd_manage as ViewCommand as *mut c_void,
        );
        BNRegisterPluginCommandForRange(
            cstr("Outliner\\Create Pattern From Selection...").as_ptr(),
            cstr("Draft a pattern for the selected MLIL: its parameters, result and shape worked out").as_ptr(),
            Some(range_action),
            None,
            cmd_draft_selection as RangeCommand as *mut c_void,
        );
        BNRegisterPluginCommandForFunction(
            cstr("Outliner\\Create Pattern From Function...").as_ptr(),
            cstr("Draft a pattern from this function's own body, as a start for its inlined form").as_ptr(),
            Some(function_action),
            None,
            cmd_draft_function as FunctionCommand as *mut c_void,
        );
        BNRegisterPluginCommandForFunction(
            cstr("Outliner\\Show Function As Pattern Text").as_ptr(),
            cstr("Render the function's MLIL in pattern syntax").as_ptr(),
            Some(function_action),
            None,
            cmd_show as FunctionCommand as *mut c_void,
        );
    }
}
