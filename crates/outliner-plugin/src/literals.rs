//! String literals for outlined calls.
//!
//! The compiler folds short string literals into immediate stores, so an
//! outlined constructor call gets its literal back as constant data
//! (`MLIL_CONST_DATA`, a zero-extended register-sized value holding the
//! characters), the same form Binary Ninja uses for the literals of its own
//! `__builtin_strncpy` outlining.  The decompiler prints constant data as
//! text only when a string recognizer claims it, so this module registers
//! one for that shape; the recognized literals also show in the strings list,
//! under their own string type.

use std::os::raw::c_void;
use std::sync::atomic::{AtomicPtr, Ordering};

use binaryninjacore_sys::*;
use outliner_core::literals::literal_text;

use crate::ffi::{cstr, Func};

pub const RECOGNIZER_NAME: &str = "Outliner literals";
pub const STRING_TYPE_NAME: &str = "Outlined literal";

const CONSTANT_DATA_ZERO_EXTEND: u64 = 32769;

static STRING_TYPE: AtomicPtr<BNCustomStringType> = AtomicPtr::new(std::ptr::null_mut());

unsafe extern "C" fn recognize_constant_data(_ctxt: *mut c_void, hlil: *mut BNHighLevelILFunction, expr: usize, result: *mut BNDerivedString) -> bool {
    let instr = BNGetHighLevelILByIndex(hlil, expr, false);
    if instr.operation != BNHighLevelILOperation::HLIL_CONST_DATA || instr.operands[0] != CONSTANT_DATA_ZERO_EXTEND {
        return false;
    }
    let Some(func) = Func::owned(BNGetHighLevelILOwnerFunction(hlil)) else { return false };
    let state: BNRegisterValueType = std::mem::transmute(instr.operands[0] as u32);
    let mut builtin = std::mem::zeroed::<BNBuiltinType>();
    let buffer = BNGetConstantData(func.raw(), state, instr.operands[1], instr.size, &mut builtin);
    if buffer.is_null() {
        return false;
    }
    let len = BNGetDataBufferLength(buffer);
    let bytes = std::slice::from_raw_parts(BNGetDataBufferContents(buffer).cast::<u8>(), len).to_vec();
    BNFreeDataBuffer(buffer);
    let Some(text) = literal_text(&bytes) else { return false };
    // A code location makes the literal a real string of the view, with
    // cross references from the instruction that assembles it.
    *result = BNDerivedString {
        value: BNCreateStringRef(cstr(&text).as_ptr()),
        locationValid: true,
        location: BNDerivedStringLocation { locationType: BNDerivedStringLocationType::CodeStringLocation, addr: instr.address, len: text.len() as u64 },
        customType: STRING_TYPE.load(Ordering::Relaxed),
    };
    true
}

/// Registers the string type and recognizer once per process; true if this call did it.
pub fn register() -> bool {
    unsafe {
        if !BNGetStringRecognizerByName(cstr(RECOGNIZER_NAME).as_ptr()).is_null() {
            return false;
        }
        let mut string_type = BNGetCustomStringTypeByName(cstr(STRING_TYPE_NAME).as_ptr());
        if string_type.is_null() {
            let name = cstr(STRING_TYPE_NAME);
            let empty = cstr("");
            let mut info = BNCustomStringTypeInfo { name: name.as_ptr() as *mut _, stringPrefix: empty.as_ptr() as *mut _, stringPostfix: empty.as_ptr() as *mut _ };
            string_type = BNRegisterCustomStringType(&mut info);
        }
        STRING_TYPE.store(string_type, Ordering::Relaxed);
        let mut recognizer = std::mem::zeroed::<BNCustomStringRecognizer>();
        recognizer.recognizeConstantData = Some(recognize_constant_data);
        !BNRegisterStringRecognizer(cstr(RECOGNIZER_NAME).as_ptr(), &mut recognizer).is_null()
    }
}
