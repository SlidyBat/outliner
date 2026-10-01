//! Thin owning wrappers over the core's C handles, and string helpers.
//!
//! Every wrapper owns one reference; `Clone` adds one and `Drop` releases it.
//! The core's objects are thread-safe, so the wrappers are `Send + Sync`.

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::ptr::NonNull;

use binaryninjacore_sys::*;

/// A C string for a call into the core (interior NULs are dropped).
pub fn cstr(text: &str) -> CString {
    CString::new(text.replace('\0', "")).expect("no interior NUL")
}

/// Copies a string the core allocated and frees it.
pub unsafe fn take_string(p: *mut c_char) -> String {
    if p.is_null() {
        return String::new();
    }
    let s = CStr::from_ptr(p).to_string_lossy().into_owned();
    BNFreeString(p);
    s
}

/// Copies a string the core still owns.
pub unsafe fn peek_string(p: *const c_char) -> String {
    if p.is_null() {
        String::new()
    } else {
        CStr::from_ptr(p).to_string_lossy().into_owned()
    }
}

macro_rules! handle {
    ($(#[$doc:meta])* $name:ident, $raw:ty, $new:ident, $free:ident) => {
        $(#[$doc])*
        pub struct $name(NonNull<$raw>);

        unsafe impl Send for $name {}
        unsafe impl Sync for $name {}

        #[allow(dead_code)]
        impl $name {
            /// Takes over a reference the core handed out.
            pub unsafe fn owned(p: *mut $raw) -> Option<Self> {
                NonNull::new(p).map(Self)
            }

            /// Adds a reference to a handle the core still owns.
            pub unsafe fn borrowed(p: *mut $raw) -> Option<Self> {
                NonNull::new(p).map(|_| Self(NonNull::new_unchecked($new(p))))
            }

            pub fn raw(&self) -> *mut $raw {
                self.0.as_ptr()
            }
        }

        impl Clone for $name {
            fn clone(&self) -> Self {
                unsafe { Self(NonNull::new_unchecked($new(self.raw()))) }
            }
        }

        impl Drop for $name {
            fn drop(&mut self) {
                unsafe { $free(self.raw()) }
            }
        }
    };
}

handle!(View, BNBinaryView, BNNewViewReference, BNFreeBinaryView);
handle!(Func, BNFunction, BNNewFunctionReference, BNFreeFunction);
handle!(Mlil, BNMediumLevelILFunction, BNNewMediumLevelILFunctionReference, BNFreeMediumLevelILFunction);
handle!(Llil, BNLowLevelILFunction, BNNewLowLevelILFunctionReference, BNFreeLowLevelILFunction);
handle!(TypeRef, BNType, BNNewTypeReference, BNFreeType);
handle!(Symbol, BNSymbol, BNNewSymbolReference, BNFreeSymbol);
handle!(Block, BNBasicBlock, BNNewBasicBlockReference, BNFreeBasicBlock);
handle!(Platform, BNPlatform, BNNewPlatformReference, BNFreePlatform);
handle!(Metadata, BNMetadata, BNNewMetadataReference, BNFreeMetadata);

impl PartialEq for TypeRef {
    fn eq(&self, other: &Self) -> bool {
        self.raw() == other.raw() || unsafe { BNTypesEqual(self.raw(), other.raw()) }
    }
}

impl View {
    pub fn session_id(&self) -> usize {
        unsafe {
            let file = BNGetFileForView(self.raw());
            if file.is_null() {
                return 0;
            }
            let id = BNFileMetadataGetSessionId(file);
            BNFreeFileMetadata(file);
            id
        }
    }

    pub fn default_platform(&self) -> Option<Platform> {
        unsafe { Platform::owned(BNGetDefaultPlatform(self.raw())) }
    }

    pub fn function_at(&self, addr: u64) -> Option<Func> {
        let platform = self.default_platform()?;
        unsafe { Func::owned(BNGetAnalysisFunction(self.raw(), platform.raw(), addr)) }
    }

    /// The function whose body holds `addr`, when there is one.
    pub fn function_containing(&self, addr: u64) -> Option<Func> {
        unsafe {
            let mut count = 0usize;
            let list = BNGetAnalysisFunctionsContainingAddress(self.raw(), addr, &mut count);
            let first = raw_list(list, count).first().and_then(|&p| Func::borrowed(p));
            BNFreeFunctionList(list, count);
            first
        }
    }

    /// Every analysed function of the view.
    pub fn functions(&self) -> Vec<Func> {
        unsafe {
            let mut count = 0usize;
            let list = BNGetAnalysisFunctionList(self.raw(), &mut count);
            let out = raw_list(list, count).iter().filter_map(|&p| Func::borrowed(p)).collect();
            BNFreeFunctionList(list, count);
            out
        }
    }

    /// The address the user is looking at.
    pub fn current_offset(&self) -> u64 {
        unsafe {
            let file = BNGetFileForView(self.raw());
            if file.is_null() {
                return 0;
            }
            let offset = BNGetCurrentOffset(file);
            BNFreeFileMetadata(file);
            offset
        }
    }

    pub fn symbol_at(&self, addr: u64) -> Option<Symbol> {
        unsafe { Symbol::owned(BNGetSymbolByAddress(self.raw(), addr, std::ptr::null())) }
    }

    pub fn symbols_at(&self, addr: u64) -> Vec<Symbol> {
        unsafe {
            let mut count = 0usize;
            let list = BNGetSymbolsInRange(self.raw(), addr, 1, &mut count, std::ptr::null());
            let out = raw_list(list, count).iter().filter_map(|&p| Symbol::borrowed(p)).collect();
            BNFreeSymbolList(list, count);
            out
        }
    }

    pub fn data_var_type_at(&self, addr: u64) -> Option<TypeRef> {
        unsafe {
            let mut var = std::mem::zeroed::<BNDataVariable>();
            if !BNGetDataVariableAtAddress(self.raw(), addr, &mut var) {
                return None;
            }
            let ty = TypeRef::borrowed(var.type_);
            BNFreeDataVariable(&mut var);
            ty
        }
    }

    /// The data variable the core reports at `addr`: its address and type.
    pub fn data_var_at(&self, addr: u64) -> Option<(u64, TypeRef)> {
        unsafe {
            let mut var = std::mem::zeroed::<BNDataVariable>();
            if !BNGetDataVariableAtAddress(self.raw(), addr, &mut var) {
                return None;
            }
            let found = TypeRef::borrowed(var.type_).map(|t| (var.address, t));
            BNFreeDataVariable(&mut var);
            found
        }
    }

    /// The start of the last data variable that begins before `addr`.
    pub fn previous_data_var_start(&self, addr: u64) -> u64 {
        unsafe { BNGetPreviousDataVariableStartBeforeAddress(self.raw(), addr) }
    }

    pub fn read(&self, addr: u64, size: usize) -> Option<Vec<u8>> {
        let mut buf = vec![0u8; size];
        let got = unsafe { BNReadViewData(self.raw(), buf.as_mut_ptr().cast(), addr, size) };
        (got == size).then_some(buf)
    }

    pub fn find_next_data(&self, start: u64, data: &[u8]) -> Option<u64> {
        unsafe {
            let buffer = BNCreateDataBuffer(data.as_ptr().cast(), data.len());
            let mut result = 0u64;
            let found = BNFindNextData(self.raw(), start, buffer, &mut result, BNFindFlag::FindCaseSensitive);
            BNFreeDataBuffer(buffer);
            found.then_some(result)
        }
    }

    pub fn start(&self) -> u64 {
        unsafe { BNGetStartOffset(self.raw()) }
    }

    pub fn end(&self) -> u64 {
        unsafe { BNGetEndOffset(self.raw()) }
    }

    pub fn has_segment_at(&self, addr: u64) -> bool {
        unsafe {
            let segment = BNGetSegmentAt(self.raw(), addr);
            if segment.is_null() {
                return false;
            }
            BNFreeSegment(segment);
            true
        }
    }

    pub fn query_metadata_string(&self, key: &str) -> Option<String> {
        unsafe {
            let data = Metadata::owned(BNBinaryViewQueryMetadata(self.raw(), cstr(key).as_ptr()))?;
            if !BNMetadataIsString(data.raw()) {
                return None;
            }
            Some(take_string(BNMetadataGetString(data.raw())))
        }
    }

    pub fn store_metadata_string(&self, key: &str, value: &str, persistent: bool) {
        unsafe {
            let data = Metadata::owned(BNCreateMetadataStringData(cstr(value).as_ptr())).expect("metadata");
            let flags = if persistent {
                BNMetadataStoreFlag::MetadataStorePersistent | BNMetadataStoreFlag::MetadataStoreMarksAnalysisChanged
            } else {
                BNMetadataStoreFlag::MetadataStoreEphemeral
            };
            BNBinaryViewStoreMetadata(self.raw(), cstr(key).as_ptr(), data.raw(), flags);
        }
    }

    pub fn reanalyze(&self) {
        unsafe { BNReanalyzeAllFunctions(self.raw()) }
    }

    /// Parses a C declaration; the type and the declared name, or the parser's message.
    pub fn parse_type(&self, text: &str) -> Result<(TypeRef, String), String> {
        unsafe {
            let mut result = std::mem::zeroed::<BNQualifiedNameAndType>();
            let mut errors: *mut c_char = std::ptr::null_mut();
            let mut allowed = std::mem::zeroed::<BNQualifiedNameList>();
            let ok = BNParseTypeString(self.raw(), cstr(text).as_ptr(), &mut result, &mut errors, &mut allowed, true);
            let message = take_string(errors);
            if !ok {
                return Err(message.trim().to_string());
            }
            let ty = TypeRef::borrowed(result.type_).ok_or_else(|| "no type".to_string())?;
            let name = qualified_name(&result.name);
            BNFreeQualifiedNameAndType(&mut result);
            Ok((ty, name))
        }
    }
}

/// The joined form of a qualified name, as the type parser spells it.
pub unsafe fn qualified_name(name: &BNQualifiedName) -> String {
    let join = peek_string(name.join);
    let join = if join.is_empty() { "::" } else { join.as_str() };
    raw_list(name.name, name.nameCount).iter().map(|&p| peek_string(p)).collect::<Vec<_>>().join(join)
}

impl Func {
    pub fn view(&self) -> Option<View> {
        unsafe { View::owned(BNGetFunctionData(self.raw())) }
    }

    pub fn start(&self) -> u64 {
        unsafe { BNGetFunctionStart(self.raw()) }
    }

    pub fn arch(&self) -> *mut BNArchitecture {
        unsafe { BNGetFunctionArchitecture(self.raw()) }
    }

    pub fn arch_name(&self) -> String {
        unsafe { take_string(BNGetArchitectureName(self.arch())) }
    }

    pub fn address_size(&self) -> usize {
        unsafe { BNGetArchitectureAddressSize(self.arch()) }
    }

    pub fn name(&self) -> String {
        unsafe {
            match Symbol::owned(BNGetFunctionSymbol(self.raw())) {
                Some(symbol) => symbol.raw_name(),
                None => format!("sub_{:x}", self.start()),
            }
        }
    }

    pub fn ty(&self) -> Option<TypeRef> {
        unsafe { TypeRef::owned(BNGetFunctionType(self.raw())) }
    }

    /// The function's MLIL, generated if it is not available yet.
    pub fn mlil(&self) -> Option<Mlil> {
        unsafe { Mlil::owned(BNGetFunctionMediumLevelIL(self.raw())) }
    }

    /// The function's MLIL when analysis has produced it.
    pub fn mlil_if_available(&self) -> Option<Mlil> {
        unsafe { Mlil::owned(BNGetFunctionMediumLevelILIfAvailable(self.raw())) }
    }

    pub fn var_name(&self, var: &BNVariable) -> String {
        unsafe { take_string(BNGetVariableName(self.raw(), var)) }
    }

    pub fn var_type(&self, var: &BNVariable) -> Option<TypeRef> {
        unsafe { TypeRef::owned(BNGetVariableType(self.raw(), var).type_) }
    }

    /// Every variable of the function with its name and type.
    pub fn variables(&self) -> Vec<(BNVariable, String, Option<TypeRef>)> {
        unsafe {
            let mut count = 0usize;
            let list = BNGetFunctionVariables(self.raw(), &mut count);
            let out = raw_list(list, count)
                .iter()
                .map(|v| (v.var, peek_string(v.name), TypeRef::borrowed(v.type_)))
                .collect();
            BNFreeVariableNameAndTypeList(list, count);
            out
        }
    }

    pub fn parameter_vars(&self) -> Vec<BNVariable> {
        unsafe {
            let mut params = BNGetFunctionParameterVariables(self.raw());
            let out = raw_list(params.vars, params.count).to_vec();
            BNFreeParameterVariables(&mut params);
            out
        }
    }

    pub fn create_auto_var(&self, var: &BNVariable, ty: &TypeRef, name: &str) {
        unsafe {
            let mut with_confidence = BNTypeWithConfidence { type_: ty.raw(), confidence: 255 };
            BNCreateAutoVariable(self.raw(), var, &mut with_confidence, cstr(name).as_ptr(), false);
        }
    }
}

impl Symbol {
    pub fn raw_name(&self) -> String {
        unsafe { take_string(BNGetSymbolRawName(self.raw())) }
    }

    pub fn short_name(&self) -> String {
        unsafe { take_string(BNGetSymbolShortName(self.raw())) }
    }

    pub fn full_name(&self) -> String {
        unsafe { take_string(BNGetSymbolFullName(self.raw())) }
    }
}

impl TypeRef {
    pub fn class(&self) -> BNTypeClass {
        unsafe { BNGetTypeClass(self.raw()) }
    }

    pub fn width(&self) -> u64 {
        unsafe { BNGetTypeWidth(self.raw()) }
    }

    pub fn is_pure(&self) -> bool {
        unsafe { BNIsTypePure(self.raw()).value }
    }

    /// The pointed-to, returned or element type.
    pub fn child(&self) -> Option<TypeRef> {
        unsafe { TypeRef::owned(BNGetChildType(self.raw()).type_) }
    }

    pub fn text(&self) -> String {
        unsafe { take_string(BNGetTypeString(self.raw(), std::ptr::null_mut(), BNTokenEscapingType::NoTokenEscapingType)) }
    }

    /// The type spelled for the parser: C++ names in backticks.
    pub fn spelling(&self) -> String {
        unsafe { take_string(BNGetTypeString(self.raw(), std::ptr::null_mut(), BNTokenEscapingType::BackticksTokenEscapingType)) }
    }

    /// The type's spelling around a name, with C++ names escaped for the parser.
    pub fn declaration(&self, name: &str) -> String {
        unsafe {
            let escaping = BNTokenEscapingType::BackticksTokenEscapingType;
            let before = take_string(BNGetTypeStringBeforeName(self.raw(), std::ptr::null_mut(), escaping));
            let after = take_string(BNGetTypeStringAfterName(self.raw(), std::ptr::null_mut(), escaping));
            format!("{before} {name}{after}")
        }
    }

    /// Parameter names of a function type.
    pub fn parameter_names(&self) -> Vec<String> {
        unsafe {
            let mut count = 0usize;
            let list = BNGetTypeParameters(self.raw(), &mut count);
            let out = raw_list(list, count).iter().map(|p| peek_string(p.name)).collect();
            BNFreeTypeParameterList(list, count);
            out
        }
    }

    /// Members of a structure type, by offset.
    pub fn members(&self) -> Vec<(u64, TypeRef)> {
        unsafe {
            let structure = BNGetTypeStructure(self.raw());
            if structure.is_null() {
                return Vec::new();
            }
            let mut count = 0usize;
            let list = BNGetStructureMembers(structure, &mut count);
            let mut out: Vec<(u64, TypeRef)> =
                raw_list(list, count).iter().filter_map(|m| TypeRef::borrowed(m.type_).map(|t| (m.offset, t))).collect();
            BNFreeStructureMemberList(list, count);
            BNFreeStructure(structure);
            out.sort_by_key(|m| m.0);
            out
        }
    }

    /// The type a named reference denotes, looked up in the view.
    pub fn resolve_named(&self, view: &View) -> Option<TypeRef> {
        unsafe {
            let reference = BNGetTypeNamedTypeReference(self.raw());
            if reference.is_null() {
                return None;
            }
            let id = take_string(BNGetTypeReferenceId(reference));
            let mut found = if id.is_empty() {
                None
            } else {
                TypeRef::owned(BNGetAnalysisTypeById(view.raw(), cstr(&id).as_ptr()))
            };
            if found.is_none() {
                let mut name = BNGetTypeReferenceName(reference);
                found = TypeRef::owned(BNGetAnalysisTypeByName(view.raw(), &mut name));
                BNFreeQualifiedName(&mut name);
            }
            BNFreeNamedTypeReference(reference);
            found
        }
    }

    pub fn pointer_to(&self, arch: *mut BNArchitecture) -> Option<TypeRef> {
        unsafe {
            let target = BNTypeWithConfidence { type_: self.raw(), confidence: 255 };
            let mut cnst = BNBoolWithConfidence { value: false, confidence: 0 };
            let mut vltl = BNBoolWithConfidence { value: false, confidence: 0 };
            TypeRef::owned(BNCreatePointerType(arch, &target, &mut cnst, &mut vltl, BNReferenceType::PointerReferenceType))
        }
    }
}

impl Mlil {
    pub fn instruction_count(&self) -> usize {
        unsafe { BNGetMediumLevelILInstructionCount(self.raw()) }
    }

    pub fn expr_count(&self) -> usize {
        unsafe { BNGetMediumLevelILExprCount(self.raw()) }
    }

    pub fn expr_for_instruction(&self, instr: usize) -> usize {
        unsafe { BNGetMediumLevelILIndexForInstruction(self.raw(), instr) }
    }

    pub fn raw_expr(&self, expr: usize) -> BNMediumLevelILInstruction {
        unsafe { BNGetMediumLevelILByIndex(self.raw(), expr) }
    }

    pub fn operand_list(&self, expr: usize, operand: usize) -> Vec<u64> {
        unsafe {
            let mut count = 0usize;
            let list = BNMediumLevelILGetOperandList(self.raw(), expr, operand, &mut count);
            let out = raw_list(list, count).to_vec();
            BNMediumLevelILFreeOperandList(list);
            out
        }
    }

    pub fn basic_blocks(&self) -> Vec<Block> {
        unsafe {
            let mut count = 0usize;
            let list = BNGetMediumLevelILBasicBlockList(self.raw(), &mut count);
            let out = raw_list(list, count).iter().filter_map(|&p| Block::borrowed(p)).collect();
            BNFreeBasicBlockList(list, count);
            out
        }
    }

    pub fn ssa_form(&self) -> Option<Mlil> {
        unsafe { Mlil::owned(BNGetMediumLevelILSSAForm(self.raw())) }
    }

    pub fn llil(&self) -> Option<Llil> {
        unsafe { Llil::owned(BNGetLowLevelILForMediumLevelIL(self.raw())) }
    }

    pub fn expr_type(&self, expr: usize) -> Option<TypeRef> {
        unsafe { TypeRef::owned(BNGetMediumLevelILExprType(self.raw(), expr).type_) }
    }

    pub fn ssa_instruction_index(&self, instr: usize) -> usize {
        unsafe { BNGetMediumLevelILSSAInstructionIndex(self.raw(), instr) }
    }

    pub fn non_ssa_instruction_index(&self, instr: usize) -> usize {
        unsafe { BNGetMediumLevelILNonSSAInstructionIndex(self.raw(), instr) }
    }

    pub fn ssa_var_version_at(&self, var: &BNVariable, instr: usize) -> usize {
        unsafe { BNGetMediumLevelILSSAVarVersionAtILInstruction(self.raw(), var, instr) }
    }

    /// The SSA instruction defining a version; None for version 0 (no definition).
    pub fn ssa_var_definition(&self, var: &BNVariable, version: usize) -> Option<usize> {
        let index = unsafe { BNGetMediumLevelILSSAVarDefinition(self.raw(), var, version) };
        (index < self.instruction_count()).then_some(index)
    }

    pub fn ssa_var_uses(&self, var: &BNVariable, version: usize) -> Vec<usize> {
        unsafe {
            let mut count = 0usize;
            let list = BNGetMediumLevelILSSAVarUses(self.raw(), var, version, &mut count);
            let out = raw_list(list, count).to_vec();
            BNFreeILInstructionList(list);
            out
        }
    }

    pub fn llil_instruction_index(&self, instr: usize) -> usize {
        unsafe { BNGetLowLevelILInstructionIndex(self.raw(), instr) }
    }

    pub fn llil_expr_index(&self, expr: usize) -> usize {
        unsafe { BNGetLowLevelILExprIndex(self.raw(), expr) }
    }

    pub fn llil_expr_indexes(&self, expr: usize) -> Vec<usize> {
        unsafe {
            let mut count = 0usize;
            let list = BNGetLowLevelILExprIndexes(self.raw(), expr, &mut count);
            let out = raw_list(list, count).to_vec();
            BNFreeILInstructionList(list);
            out
        }
    }
}

impl Llil {
    pub fn ssa_form(&self) -> Option<Llil> {
        unsafe { Llil::owned(BNGetLowLevelILSSAForm(self.raw())) }
    }

    pub fn mlil_expr_index(&self, expr: usize) -> usize {
        unsafe { BNGetMediumLevelILExprIndex(self.raw(), expr) }
    }

    pub fn mlil_expr_indexes(&self, expr: usize) -> Vec<usize> {
        unsafe {
            let mut count = 0usize;
            let list = BNGetMediumLevelILExprIndexes(self.raw(), expr, &mut count);
            let out = raw_list(list, count).to_vec();
            BNFreeILInstructionList(list);
            out
        }
    }
}

impl Block {
    pub fn start(&self) -> u64 {
        unsafe { BNGetBasicBlockStart(self.raw()) }
    }

    pub fn end(&self) -> u64 {
        unsafe { BNGetBasicBlockEnd(self.raw()) }
    }

    pub fn index(&self) -> usize {
        unsafe { BNGetBasicBlockIndex(self.raw()) }
    }

    /// Outgoing edges: (branch type, target block start).
    pub fn outgoing(&self) -> Vec<(BNBranchType, Option<u64>)> {
        unsafe {
            let mut count = 0usize;
            let list = BNGetBasicBlockOutgoingEdges(self.raw(), &mut count);
            let out = raw_list(list, count)
                .iter()
                .map(|e| (e.type_, (!e.target.is_null()).then(|| BNGetBasicBlockStart(e.target))))
                .collect();
            BNFreeBasicBlockEdgeList(list, count);
            out
        }
    }
}

/// A slice over a list the core returned (empty for a null pointer).
pub unsafe fn raw_list<'a, T>(p: *mut T, count: usize) -> &'a [T] {
    if p.is_null() || count == 0 {
        &[]
    } else {
        std::slice::from_raw_parts(p, count)
    }
}

pub fn var_identifier(var: &BNVariable) -> u64 {
    unsafe { BNToVariableIdentifier(var) }
}

pub fn var_from_identifier(id: u64) -> BNVariable {
    unsafe { BNFromVariableIdentifier(id) }
}

// --------------------------------------------------------------------------- locations

#[repr(C)]
struct DlInfo {
    dli_fname: *const c_char,
    dli_fbase: *mut std::os::raw::c_void,
    dli_sname: *const c_char,
    dli_saddr: *mut std::os::raw::c_void,
}

extern "C" {
    fn dladdr(addr: *const std::os::raw::c_void, info: *mut DlInfo) -> std::os::raw::c_int;
}

/// The path of the loaded plugin library.
pub fn plugin_path() -> Option<String> {
    unsafe {
        let mut info = std::mem::zeroed::<DlInfo>();
        if dladdr(plugin_path as *const std::os::raw::c_void, &mut info) == 0 || info.dli_fname.is_null() {
            return None;
        }
        Some(peek_string(info.dli_fname))
    }
}

/// Binary Ninja's user directory (the plugin folder's parent).
pub fn user_directory() -> String {
    unsafe { take_string(BNGetUserDirectory()) }
}

// --------------------------------------------------------------------------- logging

pub const LOGGER: &str = "Outliner";

pub fn log(level: BNLogLevel, message: &str) {
    unsafe { BNLogString(0, level, cstr(LOGGER).as_ptr(), 0, cstr(message).as_ptr()) }
}

pub fn log_debug(message: &str) {
    log(BNLogLevel::DebugLog, message)
}

pub fn log_info(message: &str) {
    log(BNLogLevel::InfoLog, message)
}

pub fn log_warn(message: &str) {
    log(BNLogLevel::WarningLog, message)
}

pub fn log_error(message: &str) {
    log(BNLogLevel::ErrorLog, message)
}
