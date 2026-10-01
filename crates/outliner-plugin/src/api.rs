//! A C API for scripts: the console can drive the plugin through `ctypes`.
//! Strings returned here are freed with [`outliner_free_string`];
//! a null result from a fallible call means success.

use std::ffi::CString;
use std::os::raw::c_char;
use std::sync::atomic::{AtomicBool, Ordering};

use binaryninjacore_sys::{BNBinaryView, BNFunction};

use outliner_core::pattern::{chunk_key, chunk_title, join_chunks, split_chunks};

use crate::commands::{function_pattern_text, timing_report, TEMPLATE};
use crate::ffi::{peek_string, Func, View};
use crate::store::{self, PatternRecord};
use crate::workflow;

/// Set once `CorePluginInit` has run, so a loader that opens the library
/// itself can tell whether the core already loaded it.
pub static INITIALIZED: AtomicBool = AtomicBool::new(false);

/// Whether the plugin has been initialised in this process.
#[no_mangle]
pub extern "C" fn outliner_initialized() -> bool {
    INITIALIZED.load(Ordering::SeqCst)
}

fn text(s: String) -> *mut c_char {
    CString::new(s.replace('\0', "")).map_or(std::ptr::null_mut(), CString::into_raw)
}

fn outcome(result: Result<(), String>) -> *mut c_char {
    match result {
        Ok(()) => std::ptr::null_mut(),
        Err(e) => text(e),
    }
}

/// Frees a string another `outliner_*` call returned.
#[no_mangle]
pub unsafe extern "C" fn outliner_free_string(s: *mut c_char) {
    if !s.is_null() {
        drop(CString::from_raw(s));
    }
}

/// The plugin's version.
#[no_mangle]
pub extern "C" fn outliner_version() -> *mut c_char {
    text(env!("CARGO_PKG_VERSION").to_string())
}

/// The manual for writing patterns (`docs/patterns.md`).
#[no_mangle]
pub extern "C" fn outliner_manual() -> *mut c_char {
    text(include_str!("../../../docs/patterns.md").to_string())
}

/// The skill that teaches AI agents to use the plugin (`skills/outliner/SKILL.md`).
#[no_mangle]
pub extern "C" fn outliner_skill() -> *mut c_char {
    text(include_str!("../../../skills/outliner/SKILL.md").to_string())
}

/// Registers a pattern (`signature` may be null to use the text's own line).
#[no_mangle]
pub unsafe extern "C" fn outliner_add_pattern(view: *mut BNBinaryView, pattern: *const c_char, signature: *const c_char, reanalyze: bool) -> *mut c_char {
    let Some(view) = View::borrowed(view) else { return text("no view".into()) };
    let signature = if signature.is_null() { None } else { Some(peek_string(signature)) };
    outcome(store::add_pattern(&view, &peek_string(pattern), signature.as_deref(), reanalyze).map(|_| ()))
}

/// Removes every pattern registered under a name (or the record with that id).
#[no_mangle]
pub unsafe extern "C" fn outliner_remove_pattern(view: *mut BNBinaryView, name: *const c_char, reanalyze: bool) -> bool {
    let Some(view) = View::borrowed(view) else { return false };
    store::remove_pattern(&view, &peek_string(name), reanalyze)
}

/// Adds the patterns of a file, skipping those already saved; null on success.
#[no_mangle]
pub unsafe extern "C" fn outliner_load_pattern_file(view: *mut BNBinaryView, path: *const c_char, reanalyze: bool) -> *mut c_char {
    let Some(view) = View::borrowed(view) else { return text("no view".into()) };
    outcome(store::load_pattern_file(&view, &peek_string(path), reanalyze).map(|_| ()))
}


#[no_mangle]
pub unsafe extern "C" fn outliner_save_pattern_file(view: *mut BNBinaryView, path: *const c_char) -> *mut c_char {
    let Some(view) = View::borrowed(view) else { return text("no view".into()) };
    outcome(store::save_pattern_file(&view, &peek_string(path)).map(|_| ()))
}

fn record_json(record: &PatternRecord) -> serde_json::Value {
    let mut value = serde_json::to_value(record).unwrap_or(serde_json::Value::Null);
    if let Some(object) = value.as_object_mut() {
        object.insert("full_text".into(), serde_json::Value::String(record.full_text()));
    }
    value
}

/// The registered patterns as a JSON list of records, each with its
/// `full_text` (the text with its signature line, as edited).
#[no_mangle]
pub unsafe extern "C" fn outliner_list_patterns(view: *mut BNBinaryView) -> *mut c_char {
    let Some(view) = View::borrowed(view) else { return text("[]".into()) };
    let records: Vec<serde_json::Value> = store::load_records(&view).iter().map(record_json).collect();
    text(serde_json::to_string(&records).unwrap_or_else(|_| "[]".into()))
}

/// Checks a complete pattern text: `{"ok": true, "record": {...}}` or
/// `{"ok": false, "error": "..."}`.
#[no_mangle]
pub unsafe extern "C" fn outliner_validate_pattern(view: *mut BNBinaryView, pattern: *const c_char) -> *mut c_char {
    let answer = match View::borrowed(view) {
        None => serde_json::json!({"ok": false, "error": "no view"}),
        Some(view) => match store::validate_text(&view, &peek_string(pattern)) {
            Ok(record) => serde_json::json!({"ok": true, "record": record_json(&record)}),
            Err(e) => serde_json::json!({"ok": false, "error": e}),
        },
    };
    text(answer.to_string())
}

/// Replaces the whole pattern list with the JSON records given (each already
/// validated with `outliner_validate_pattern`); null on success.
#[no_mangle]
pub unsafe extern "C" fn outliner_save_patterns(view: *mut BNBinaryView, records: *const c_char, reanalyze: bool) -> *mut c_char {
    let Some(view) = View::borrowed(view) else { return text("no view".into()) };
    let records: Vec<PatternRecord> = match serde_json::from_str(&peek_string(records)) {
        Ok(records) => records,
        Err(e) => return text(format!("bad record list: {e}")),
    };
    outcome(store::save_records(&view, records, reanalyze))
}

/// The chunks of a pattern file's text, as a JSON list.
#[no_mangle]
pub unsafe extern "C" fn outliner_split_chunks(content: *const c_char) -> *mut c_char {
    text(serde_json::to_string(&split_chunks(&peek_string(content))).unwrap_or_else(|_| "[]".into()))
}

/// A pattern file's text for a JSON list of chunks.
#[no_mangle]
pub unsafe extern "C" fn outliner_join_chunks(chunks: *const c_char) -> *mut c_char {
    let chunks: Vec<String> = serde_json::from_str(&peek_string(chunks)).unwrap_or_default();
    text(join_chunks(&chunks))
}

/// What decides whether two pattern texts are the same pattern: equal keys
/// (comments and spacing do not count).  Used by the pattern editor.
#[no_mangle]
pub unsafe extern "C" fn outliner_chunk_key(pattern: *const c_char) -> *mut c_char {
    text(chunk_key(&peek_string(pattern)))
}

/// The title a pattern text shows in the manager.
#[no_mangle]
pub unsafe extern "C" fn outliner_chunk_title(pattern: *const c_char) -> *mut c_char {
    text(chunk_title(&peek_string(pattern)))
}

/// The text a new pattern starts from.
#[no_mangle]
pub extern "C" fn outliner_pattern_template() -> *mut c_char {
    text(TEMPLATE.to_string())
}

/// The function's MLIL in pattern syntax, with its signature spelled for the type parser.
#[no_mangle]
pub unsafe extern "C" fn outliner_function_pattern_text(func: *mut BNFunction) -> *mut c_char {
    let Some(func) = Func::borrowed(func) else { return text(String::new()) };
    let Some(view) = func.view() else { return text(String::new()) };
    text(function_pattern_text(&view, &func))
}

#[no_mangle]
pub extern "C" fn outliner_reset_timing() {
    workflow::reset_stats();
}

/// The activity's timing records since the last reset, as JSON.
#[no_mangle]
pub extern "C" fn outliner_timing_json() -> *mut c_char {
    text(serde_json::to_string(&workflow::take_stats()).unwrap_or_else(|_| "[]".into()))
}

/// The timing report as text.
#[no_mangle]
pub extern "C" fn outliner_timing_report() -> *mut c_char {
    text(timing_report(&workflow::take_stats()))
}

/// How many times a view's patterns were compiled since the plugin loaded.
#[no_mangle]
pub extern "C" fn outliner_compile_count() -> usize {
    store::COMPILES.load(Ordering::Relaxed)
}

// --------------------------------------------------------------------------- drafting and preview

/// Drafts a pattern for the MLIL instructions in `[start, end)` of the
/// function holding `start` (JSON: ok, text, notes, function, start, end, error).
#[no_mangle]
pub unsafe extern "C" fn outliner_draft_region(view: *mut BNBinaryView, start: u64, end: u64) -> *mut c_char {
    let Some(view) = View::borrowed(view) else { return text("{\"ok\":false,\"error\":\"no view\"}".into()) };
    text(serde_json::to_string(&crate::analysis::draft_selection(&view, start, end)).unwrap_or_default())
}

/// Drafts a pattern for MLIL instructions `first..=last` of the function at `func`.
#[no_mangle]
pub unsafe extern "C" fn outliner_draft_indices(view: *mut BNBinaryView, func: u64, first: u32, last: u32) -> *mut c_char {
    let Some(view) = View::borrowed(view) else { return text("{\"ok\":false,\"error\":\"no view\"}".into()) };
    text(serde_json::to_string(&crate::analysis::draft_indices(&view, func, first, last)).unwrap_or_default())
}

/// Drafts a pattern from the whole function at `addr` (its out-of-line body).
#[no_mangle]
pub unsafe extern "C" fn outliner_draft_function(view: *mut BNBinaryView, addr: u64) -> *mut c_char {
    let Some(view) = View::borrowed(view) else { return text("{\"ok\":false,\"error\":\"no view\"}".into()) };
    text(serde_json::to_string(&crate::analysis::draft_whole_function(&view, addr)).unwrap_or_default())
}

/// The function starts of a JSON list (null or empty: none).
unsafe fn addresses(json: *const c_char) -> Vec<u64> {
    if json.is_null() {
        return Vec::new();
    }
    serde_json::from_str::<Option<Vec<u64>>>(&peek_string(json)).ok().flatten().unwrap_or_default()
}

/// The text indices of a JSON list (null: every text).
unsafe fn indices(json: *const c_char) -> Option<Vec<usize>> {
    if json.is_null() {
        return None;
    }
    serde_json::from_str::<Option<Vec<usize>>>(&peek_string(json)).ok().flatten()
}

/// Runs pattern texts (a JSON list) over every function without rewriting,
/// and blocks until done.  `focus` is a JSON list of function starts where
/// each reported pattern that does not match is explained; `report` a JSON
/// list of the indices of the texts to report, the others taking part
/// unreported (null: all).
#[no_mangle]
pub unsafe extern "C" fn outliner_preview(view: *mut BNBinaryView, texts: *const c_char, focus: *const c_char, report: *const c_char) -> *mut c_char {
    let Some(view) = View::borrowed(view) else { return text("{\"patterns\":[],\"functions\":0}".into()) };
    let texts: Vec<String> = serde_json::from_str(&peek_string(texts)).unwrap_or_default();
    text(serde_json::to_string(&crate::analysis::preview(&view, &texts, addresses(focus), indices(report))).unwrap_or_default())
}

/// [`outliner_preview`] in the background; returns its job id (0 on failure).
#[no_mangle]
pub unsafe extern "C" fn outliner_preview_start(view: *mut BNBinaryView, texts: *const c_char, focus: *const c_char, report: *const c_char) -> u64 {
    let Some(view) = View::borrowed(view) else { return 0 };
    let texts: Vec<String> = serde_json::from_str(&peek_string(texts)).unwrap_or_default();
    crate::analysis::start_preview(&view, texts, addresses(focus), indices(report))
}

/// Where a test got to: JSON `{"done", "processed", "total", "cancelled"}`.
#[no_mangle]
pub extern "C" fn outliner_preview_poll(id: u64) -> *mut c_char {
    let answer = match crate::analysis::job(id) {
        Some(job) => serde_json::json!({
            "done": job.done.load(Ordering::SeqCst),
            "processed": job.processed.load(Ordering::Relaxed),
            "total": job.total.load(Ordering::Relaxed),
            "cancelled": job.cancel.load(Ordering::Relaxed),
        }),
        None => serde_json::json!({"done": true, "processed": 0, "total": 0, "cancelled": false, "error": "no such job"}),
    };
    text(answer.to_string())
}

/// Asks a running test to stop after the functions in hand; its result then
/// covers what was tested.
#[no_mangle]
pub extern "C" fn outliner_preview_cancel(id: u64) {
    if let Some(job) = crate::analysis::job(id) {
        job.cancel.store(true, Ordering::SeqCst);
    }
}

/// A finished test's result (the preview JSON), forgetting the job; empty
/// until the job is done.
#[no_mangle]
pub extern "C" fn outliner_preview_result(id: u64) -> *mut c_char {
    let Some(job) = crate::analysis::job(id) else { return text("{}".into()) };
    if !job.done.load(Ordering::SeqCst) {
        return text("{}".into());
    }
    crate::analysis::forget_job(id);
    text(job.take_result().and_then(|p| serde_json::to_string(&p).ok()).unwrap_or_else(|| "{}".into()))
}

/// Generalises a pattern with a second instance of its code (JSON: kind
/// "merged" with the new text and notes, "chunk" with the instance as a shape
/// of its own, or "error").
#[no_mangle]
pub unsafe extern "C" fn outliner_generalize(base: *const c_char, other: *const c_char) -> *mut c_char {
    text(serde_json::to_string(&crate::analysis::merge(&peek_string(base), &peek_string(other))).unwrap_or_default())
}
