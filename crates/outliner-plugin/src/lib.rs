//! Outliner: turn inlined code back into function calls.
//!
//! Users describe an MLIL fragment as a text pattern together with a C
//! function signature.  During analysis every match is replaced with a call
//! to a function of that signature.  The pattern language, matcher and
//! rewrite planner live in `outliner-core`; this crate binds them to Binary
//! Ninja through the C API.

mod analysis;
mod api;
mod commands;
mod env;
mod ffi;
mod literals;
mod rewrite;
mod snapshot;
mod store;
mod types;
mod workflow;

use binaryninjacore_sys::BN_CURRENT_CORE_ABI_VERSION;

use crate::ffi::log_error;

#[no_mangle]
pub extern "C" fn CorePluginABIVersion() -> u32 {
    BN_CURRENT_CORE_ABI_VERSION
}

#[no_mangle]
pub extern "C" fn CorePluginInit() -> bool {
    if api::INITIALIZED.swap(true, std::sync::atomic::Ordering::SeqCst) {
        return true; // loaded a second time (the core and a loader): already registered
    }
    if let Err(e) = workflow::register() {
        log_error(&format!("Outliner failed to initialize: {e}"));
        return false;
    }
    commands::register();
    if !literals::register() {
        log_error("Outliner could not register its literal recognizer");
    }
    true
}
