//! Persist patterns in the BinaryView and manage the call targets they outline to.
//!
//! Patterns live in the view's metadata (so they are saved in the .bndb).
//! Each pattern gets an "outlined" function: an external symbol plus a
//! function-typed data variable in a synthetic `outlined` section, exactly like an imported function in a
//! Mach-O `extern` segment.  Calls emitted by the rewriter target that
//! address, so the decompiler shows `name(args)` with the user's signature.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, LazyLock, Mutex, MutexGuard};

use binaryninjacore_sys::*;
use outliner_core::pattern::{join_chunks, split_chunks, parse_pattern, ChunkSet, Pattern, Rule};
use serde::{Deserialize, Serialize};

use crate::ffi::{cstr, log_error, log_info, log_warn, TypeRef, View};

pub const KEY_PATTERNS: &str = "outliner.patterns";
pub const KEY_TARGETS: &str = "outliner.targets";
pub const KEY_BASE: &str = "outliner.base";

pub const SECTION_NAME: &str = "outlined";
pub const REGION_SIZE: u64 = 0x10000;
pub const TARGET_STRIDE: u64 = 0x10;
pub const RULES_DEFAULT_NAME: &str = "rewrite rules";

/// Entries kept per per-view cache; closed views' entries age out.
const CACHE_VIEWS: usize = 8;
const CACHE_SIGNATURES: usize = 512;

/// `SegmentReadable | SegmentExecutable`.
const SEGMENT_FLAGS: u32 = 4 | 1;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PatternRecord {
    pub name: String,
    pub signature: String,
    pub text: String,
    #[serde(default)]
    pub id: String,
    /// "pattern" or "rules".
    #[serde(default = "pattern_kind")]
    pub kind: String,
}

fn pattern_kind() -> String {
    "pattern".to_string()
}

impl PatternRecord {
    pub fn is_rules(&self) -> bool {
        self.kind == "rules"
    }

    /// The pattern text with its signature line, as edited by the user.
    pub fn full_text(&self) -> String {
        let has_line = self.text.lines().any(|l| l.trim_start().starts_with("signature") && l.contains(':'));
        if self.is_rules() || self.signature.is_empty() || has_line {
            return self.text.clone();
        }
        format!("signature: {}\n{}", self.signature, self.text.trim_start())
    }
}

/// A parsed signature: the function type, its name, parameter names, whether
/// it returns a value and whether it is `__pure`.
pub struct Signature {
    pub ty: TypeRef,
    pub name: String,
    pub params: Vec<String>,
    pub returns: bool,
    pub pure: bool,
}

/// The patterns of a view, compiled: the outlining patterns and every rule.
pub struct Compiled {
    pub patterns: Vec<Pattern>,
    pub rules: Vec<Rule>,
}

/// What the per-view caches are keyed on: a file's views share a session but
/// each keeps its own metadata.
type ViewKey = (usize, usize);

/// Per-view caches.  The workflow activity consults them on every function
/// analysed, so a lookup must not go through the view: querying the metadata
/// to validate the cache took the view's lock on every analysis thread at
/// once, and that wait cost more than the matching itself.  The writers in
/// this module invalidate them; they are the only writers of the plugin's
/// metadata, and a reopened file gets a new session.
type ViewCache<T> = Mutex<Vec<(ViewKey, Arc<T>)>>;
static COMPILED: ViewCache<Compiled> = Mutex::new(Vec::new());
static TARGETS: ViewCache<HashMap<String, u64>> = Mutex::new(Vec::new());
/// Parsed signatures and type constraints by (session, text).  The core's
/// type parser costs tens of milliseconds per call, so two dozen signatures
/// took a second to compile; registering a pattern parses its
/// signature to validate it, and the compile that follows reuses that parse.
type SessionCache<T> = LazyLock<Mutex<HashMap<(usize, String), T>>>;
static SIGNATURES: SessionCache<Arc<Signature>> = LazyLock::new(|| Mutex::new(HashMap::new()));
static TYPES: SessionCache<Option<TypeRef>> = LazyLock::new(|| Mutex::new(HashMap::new()));
/// Pattern compilations so far.
pub static COMPILES: AtomicUsize = AtomicUsize::new(0);
/// Serialises the writers of the plugin's metadata.
static WRITE_LOCK: Mutex<()> = Mutex::new(());

/// The MLIL each outlined function had before the activity rewrote it, per
/// view: what the manager's Test matches against, since the function's
/// current MLIL no longer holds the code the patterns describe.
static ORIGINALS: Mutex<Vec<(ViewKey, HashMap<u64, crate::ffi::Mlil>)>> = Mutex::new(Vec::new());

/// Keeps the MLIL the activity found `function` with (its start address).
pub fn remember_original(view: &View, function: u64, mlil: crate::ffi::Mlil) {
    let key = view_key(view);
    let mut views = lock(&ORIGINALS);
    if let Some((_, map)) = views.iter_mut().find(|(k, _)| *k == key) {
        map.insert(function, mlil);
        return;
    }
    while views.len() >= CACHE_VIEWS {
        views.remove(0);
    }
    views.push((key, HashMap::from([(function, mlil)])));
}

/// The function was analysed and nothing was outlined: its current MLIL is the original.
pub fn forget_original(view: &View, function: u64) {
    let key = view_key(view);
    if let Some((_, map)) = lock(&ORIGINALS).iter_mut().find(|(k, _)| *k == key) {
        map.remove(&function);
    }
}

/// The MLIL `function` had before outlining, when it was outlined.
pub fn original_mlil(view: &View, function: u64) -> Option<crate::ffi::Mlil> {
    let key = view_key(view);
    lock(&ORIGINALS).iter().find(|(k, _)| *k == key).and_then(|(_, map)| map.get(&function).cloned())
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(|e| e.into_inner())
}

fn view_key(view: &View) -> ViewKey {
    (view.session_id(), view.raw() as usize)
}

fn lookup<T: Clone>(entries: &[(ViewKey, T)], key: ViewKey) -> Option<T> {
    entries.iter().find(|(k, _)| *k == key).map(|(_, v)| v.clone())
}

fn remember<T>(entries: &mut Vec<(ViewKey, T)>, key: ViewKey, value: T) {
    entries.retain(|(k, _)| *k != key);
    while entries.len() >= CACHE_VIEWS {
        entries.remove(0);
    }
    entries.push((key, value));
}

fn forget_compiled() {
    lock(&COMPILED).clear();
}

// --------------------------------------------------------------------------- metadata

fn load_json<T: for<'de> Deserialize<'de>>(view: &View, key: &str) -> Option<T> {
    serde_json::from_str(&view.query_metadata_string(key)?).ok()
}

fn store_json<T: Serialize>(view: &View, key: &str, value: &T) {
    view.store_metadata_string(key, &serde_json::to_string(value).unwrap_or_default(), true);
}

/// A unique record id: 32 hexadecimal digits.
fn fresh_id() -> String {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    format!("{:016x}{:016x}", nanos as u64 ^ (std::process::id() as u64) << 40, n.rotate_left(17) ^ (nanos >> 64) as u64)
}

pub fn load_records(view: &View) -> Vec<PatternRecord> {
    let mut records: Vec<PatternRecord> = load_json(view, KEY_PATTERNS).unwrap_or_default();
    for r in &mut records {
        if r.id.is_empty() {
            r.id = fresh_id();
        }
    }
    records
}

fn save_records_raw(view: &View, records: &mut [PatternRecord]) {
    for r in records.iter_mut() {
        if r.id.is_empty() {
            r.id = fresh_id();
        }
    }
    store_json(view, KEY_PATTERNS, &records);
}

/// Replace the whole pattern list.  Every record must already be validated
/// with [`validate_text`].
pub fn save_records(view: &View, mut records: Vec<PatternRecord>, reanalyze: bool) -> Result<(), String> {
    {
        let _guard = lock(&WRITE_LOCK);
        let mut signatures = Vec::with_capacity(records.len());
        for r in &mut records {
            if r.is_rules() {
                continue;
            }
            let signature = parse_signature(view, &r.signature)?;
            r.name = signature.name.clone();
            signatures.push((r.signature.clone(), signature));
        }
        // Targets of deleted, renamed or retyped patterns go first, so a
        // renamed function takes the slot its old name held.
        prune_targets(view, &target_keys(&records));
        for (text, signature) in &signatures {
            ensure_target(view, text, &signature.name, &signature.ty)?;
        }
        save_records_raw(view, &mut records);
        forget_compiled();
    }
    if reanalyze {
        view.reanalyze();
    }
    Ok(())
}

/// Parse and check a complete pattern text (with its `signature:` line, or a
/// rules chunk); returns an unsaved record, or a message for the user.
pub fn validate_text(view: &View, text: &str) -> Result<PatternRecord, String> {
    let mut pattern = parse_pattern(text).map_err(|e| e.to_string())?;
    if pattern.is_rules() {
        let name = pattern.rules_name.clone().unwrap_or_else(|| RULES_DEFAULT_NAME.to_string());
        return Ok(PatternRecord { name, signature: String::new(), text: text.to_string(), id: String::new(), kind: "rules".into() });
    }
    let Some(sig) = pattern.signature.clone() else {
        return Err("the pattern needs a 'signature:' line".to_string());
    };
    let signature = parse_signature(view, &sig)?;
    pattern.name = signature.name.clone();
    pattern
        .validate_signature(&signature.params, signature.returns, signature.pure, Some(&signature.name))
        .map_err(|e| e.to_string())?;
    Ok(PatternRecord { name: signature.name.clone(), signature: sig, text: text.to_string(), id: String::new(), kind: pattern_kind() })
}

// --------------------------------------------------------------------------- signatures / types

/// The parsed signature, memoized per session (a signature that does not
/// parse is not).
pub fn parse_signature(view: &View, signature: &str) -> Result<Arc<Signature>, String> {
    let key = (view.session_id(), signature.to_string());
    if let Some(cached) = lock(&SIGNATURES).get(&key) {
        return Ok(cached.clone());
    }
    let parsed = Arc::new(parse_signature_uncached(view, signature)?);
    let mut signatures = lock(&SIGNATURES);
    if signatures.len() >= CACHE_SIGNATURES {
        signatures.clear();
    }
    signatures.insert(key, parsed.clone());
    Ok(parsed)
}

fn parse_signature_uncached(view: &View, signature: &str) -> Result<Signature, String> {
    let (ty, name) = view.parse_type(signature).map_err(|e| {
        let hint = if signature.contains("::") || signature.contains('<') {
            " (C++ names must be wrapped in backticks, the function's own name included, e.g. \
             uint64_t `std::string::size`(`std::__1::string` const* s); \
             use 'Outliner > Show Function As Pattern Text' to see the exact type spelling)"
        } else {
            ""
        };
        format!("cannot parse signature {signature:?}: {e}{hint}")
    })?;
    if ty.class() != BNTypeClass::FunctionTypeClass {
        return Err(format!("signature {signature:?} is not a function declaration"));
    }
    if name.is_empty() {
        return Err("the signature must name the function".to_string());
    }
    let params = ty.parameter_names();
    let returns = ty.child().is_some_and(|r| r.class() != BNTypeClass::VoidTypeClass);
    let pure = ty.is_pure();
    Ok(Signature { ty, name, params, returns, pure })
}

/// Parse a type constraint; None if it is a /regex/ or does not parse (then
/// it is compared textually against the printed type).
pub fn parse_type_cached(view: &View, text: &str) -> Option<TypeRef> {
    let key = (view.session_id(), text.to_string());
    if let Some(cached) = lock(&TYPES).get(&key) {
        return cached.clone();
    }
    let is_regex = text.len() >= 2 && text.starts_with('/') && text.ends_with('/');
    let result = if is_regex {
        None
    } else {
        match view.parse_type(text) {
            Ok((ty, _)) => Some(ty),
            Err(e) => {
                log_warn(&format!("type constraint {text:?} does not parse ({e}); comparing it as text"));
                None
            }
        }
    };
    let mut types = lock(&TYPES);
    if types.len() >= CACHE_SIGNATURES {
        types.clear();
    }
    types.insert(key, result.clone());
    result
}

/// Compiles a pattern text as the manager holds it (with its signature line),
/// without saving it: what the preview runs.
pub fn compile_text(view: &View, text: &str) -> Result<Pattern, String> {
    let record = validate_text(view, text)?;
    compile_record(view, &record)
}

fn compile_record(view: &View, record: &PatternRecord) -> Result<Pattern, String> {
    let mut pattern = parse_pattern(&record.text).map_err(|e| e.to_string())?;
    if pattern.is_rules() {
        pattern.name = record.name.clone();
        return Ok(pattern);
    }
    let signature = parse_signature(view, &record.signature)?;
    pattern.name = signature.name.clone();
    pattern.signature = Some(record.signature.clone());
    pattern
        .validate_signature(&signature.params, signature.returns, signature.pure, Some(&signature.name))
        .map_err(|e| e.to_string())?;
    Ok(pattern)
}

/// The view's patterns, compiled once per view.  The lock is held across a
/// compilation so that the analysis threads, which all ask at once when the
/// cache is cold, compile once between them.
pub fn compiled_patterns(view: &View) -> Arc<Compiled> {
    let key = view_key(view);
    let mut compiled_views = lock(&COMPILED);
    if let Some(cached) = lookup(&compiled_views, key) {
        return cached;
    }
    let mut patterns = Vec::new();
    let mut rules = Vec::new();
    for record in load_records(view) {
        match compile_record(view, &record) {
            Ok(mut pattern) => {
                rules.append(&mut pattern.rules);
                if !pattern.is_rules() {
                    patterns.push(pattern);
                }
            }
            Err(e) => log_error(&format!("pattern {:?} is invalid and will be ignored: {e}", record.name)),
        }
    }
    COMPILES.fetch_add(1, Ordering::Relaxed);
    let compiled = Arc::new(Compiled { patterns, rules });
    remember(&mut compiled_views, key, compiled.clone());
    compiled
}

// --------------------------------------------------------------------------- call targets

fn region_base(view: &View) -> u64 {
    if let Some(base) = load_json::<u64>(view, KEY_BASE) {
        if view.has_segment_at(base) {
            return base;
        }
    }
    let align = 0x10000u64;
    let mut candidate = (view.end() + 0x100000 + align - 1) & !(align - 1);
    while view.has_segment_at(candidate) || view.has_segment_at(candidate + REGION_SIZE - 1) {
        candidate += align;
    }
    unsafe {
        BNAddUserSegment(view.raw(), candidate, REGION_SIZE, 0, 0, SEGMENT_FLAGS);
        let empty = cstr("");
        BNAddUserSection(
            view.raw(),
            cstr(SECTION_NAME).as_ptr(),
            candidate,
            REGION_SIZE,
            BNSectionSemantics::ExternalSectionSemantics,
            empty.as_ptr(),
            1,
            1,
            empty.as_ptr(),
            empty.as_ptr(),
            0,
        );
    }
    store_json(view, KEY_BASE, &candidate);
    log_info(&format!("created section '{SECTION_NAME}' at {candidate:#x} for outlined functions"));
    candidate
}

/// Call targets are one per signature, so a name may be overloaded
/// (`std::string::string` for each constructor).
pub fn target_key(signature: &str) -> String {
    signature.split_whitespace().collect()
}

/// Make sure an external function `name` with `ty` exists for this
/// `signature`; return its address.
pub fn ensure_target(view: &View, signature: &str, name: &str, ty: &TypeRef) -> Result<u64, String> {
    let key = target_key(signature);
    let mut targets: HashMap<String, u64> = (*targets(view)).clone();
    let base = region_base(view);
    let addr = match targets.get(&key) {
        Some(addr) => *addr,
        None => {
            let used: HashSet<u64> = targets.values().copied().collect();
            let mut addr = base;
            while used.contains(&addr) {
                addr += TARGET_STRIDE;
            }
            if addr >= base + REGION_SIZE {
                return Err("too many outlined functions".to_string());
            }
            targets.insert(key, addr);
            store_json(view, KEY_TARGETS, &targets);
            remember(&mut lock(&TARGETS), view_key(view), Arc::new(targets));
            addr
        }
    };
    let named = view.symbol_at(addr).is_some_and(|s| s.raw_name() == name);
    if !named {
        unsafe {
            let cname = cstr(name);
            let symbol = BNCreateSymbol(
                BNSymbolType::ExternalSymbol,
                cname.as_ptr(),
                cname.as_ptr(),
                cname.as_ptr(),
                addr,
                BNSymbolBinding::NoBinding,
                std::ptr::null(),
                0,
            );
            BNDefineUserSymbol(view.raw(), symbol);
            BNFreeSymbol(symbol);
        }
    }
    let typed = view.data_var_type_at(addr).is_some_and(|t| &t == ty);
    if !typed {
        unsafe {
            let mut with_confidence = BNTypeWithConfidence { type_: ty.raw(), confidence: 255 };
            BNDefineUserDataVariable(view.raw(), addr, &mut with_confidence);
        }
    }
    Ok(addr)
}

/// The signature keys of the records that outline to a call target.
fn target_keys(records: &[PatternRecord]) -> HashSet<String> {
    records.iter().filter(|r| !r.is_rules()).map(|r| target_key(&r.signature)).collect()
}

/// Drops the call targets no record in `keep` uses any more (a pattern was
/// deleted, or its signature renamed or retyped): their external symbol and
/// function-typed data variable go, and their slots in the section are the
/// first ones [`ensure_target`] hands out again.  Returns what was dropped.
fn prune_targets(view: &View, keep: &HashSet<String>) -> Vec<(String, u64)> {
    let mut targets: HashMap<String, u64> = (*targets(view)).clone();
    let stale: Vec<(String, u64)> = targets.iter().filter(|(k, _)| !keep.contains(*k)).map(|(k, a)| (k.clone(), *a)).collect();
    if stale.is_empty() {
        return stale;
    }
    let mut dropped = Vec::new();
    for (key, addr) in &stale {
        targets.remove(key);
        let name = view.symbol_at(*addr).map(|s| s.raw_name()).unwrap_or_default();
        unsafe {
            for symbol in view.symbols_at(*addr) {
                BNUndefineUserSymbol(view.raw(), symbol.raw());
            }
            BNUndefineUserDataVariable(view.raw(), *addr);
        }
        log_info(&format!("released call target {name:?} at {addr:#x}"));
        dropped.push((name, *addr));
    }
    store_json(view, KEY_TARGETS, &targets);
    remember(&mut lock(&TARGETS), view_key(view), Arc::new(targets));
    dropped
}

/// The view's call targets by signature key, cached per view.
pub fn targets(view: &View) -> Arc<HashMap<String, u64>> {
    let key = view_key(view);
    let mut target_views = lock(&TARGETS);
    if let Some(cached) = lookup(&target_views, key) {
        return cached;
    }
    let loaded: HashMap<String, u64> = load_json::<HashMap<String, serde_json::Value>>(view, KEY_TARGETS)
        .unwrap_or_default()
        .into_iter()
        .filter_map(|(k, v)| v.as_u64().map(|a| (k, a)))
        .collect();
    let loaded = Arc::new(loaded);
    remember(&mut target_views, key, loaded.clone());
    loaded
}

/// Addresses of every outlined call target registered in this view.
pub fn target_addresses(view: &View) -> HashSet<u64> {
    targets(view).values().copied().collect()
}

/// The call target of a pattern: its address and function type.
pub fn resolve_target(view: &View, pattern: &Pattern) -> Option<(u64, TypeRef)> {
    let signature = pattern.signature.as_deref()?;
    let addr = *targets(view).get(&target_key(signature))?;
    Some((addr, view.data_var_type_at(addr)?))
}

// --------------------------------------------------------------------------- public API

/// A chunk checked and ready to save.
enum Prepared {
    Rules { name: String },
    Pattern { signature: String, parsed: Arc<Signature> },
}

/// Parse and check one chunk; `signature` overrides its `signature:` line.
fn prepare(view: &View, text: &str, signature: Option<&str>) -> Result<Prepared, String> {
    let mut pattern = parse_pattern(text).map_err(|e| e.to_string())?;
    if pattern.is_rules() {
        return Ok(Prepared::Rules { name: pattern.rules_name.clone().unwrap_or_else(|| RULES_DEFAULT_NAME.to_string()) });
    }
    let sig = match signature.map(str::trim).filter(|s| !s.is_empty()) {
        Some(s) => s.to_string(),
        None => pattern.signature.clone().unwrap_or_default(),
    };
    if sig.is_empty() {
        return Err("no function signature given (pass one or add a 'signature:' line)".to_string());
    }
    let parsed = parse_signature(view, &sig)?;
    pattern.name = parsed.name.clone();
    pattern.validate_signature(&parsed.params, parsed.returns, parsed.pure, Some(&parsed.name)).map_err(|e| e.to_string())?;
    Ok(Prepared::Pattern { signature: sig, parsed })
}

/// Save a checked chunk; returns its name.
fn save_prepared(view: &View, text: &str, prepared: Prepared) -> Result<String, String> {
    match prepared {
        Prepared::Rules { name } => {
            {
                let _guard = lock(&WRITE_LOCK);
                let mut records: Vec<PatternRecord> =
                    load_records(view).into_iter().filter(|r| !(r.is_rules() && r.text.trim() == text.trim())).collect();
                records.push(PatternRecord { name: name.clone(), signature: String::new(), text: text.to_string(), id: fresh_id(), kind: "rules".into() });
                save_records_raw(view, &mut records);
                forget_compiled();
            }
            log_info(&format!("registered rewrite rules {name:?}"));
            Ok(name)
        }
        Prepared::Pattern { signature: sig, parsed } => {
            {
                let _guard = lock(&WRITE_LOCK);
                // Several chunks may share a signature (shapes of one function), and a
                // name may have several signatures (overloads); identical text is one record.
                let mut records: Vec<PatternRecord> =
                    load_records(view).into_iter().filter(|r| !(r.name == parsed.name && r.text.trim() == text.trim())).collect();
                records.push(PatternRecord { name: parsed.name.clone(), signature: sig.clone(), text: text.to_string(), id: fresh_id(), kind: pattern_kind() });
                prune_targets(view, &target_keys(&records));
                ensure_target(view, &sig, &parsed.name, &parsed.ty)?;
                save_records_raw(view, &mut records);
                forget_compiled();
            }
            log_info(&format!("registered outlining pattern {:?}", parsed.name));
            Ok(parsed.name.clone())
        }
    }
}

/// Validate and register a pattern, or several separated by lines holding
/// only `---`: every one is checked before any is saved, and analysis runs
/// once.  `signature` overrides the `signature:` line of each.  Returns the
/// names registered.
pub fn add_pattern(view: &View, text: &str, signature: Option<&str>, reanalyze: bool) -> Result<String, String> {
    let chunks: Vec<String> = split_chunks(text).into_iter().filter(|c| !c.trim().is_empty()).collect();
    if chunks.is_empty() {
        return Err("the text holds no pattern".to_string());
    }
    let several = chunks.len() > 1;
    let mut prepared = Vec::with_capacity(chunks.len());
    for (k, chunk) in chunks.iter().enumerate() {
        prepared.push(prepare(view, chunk, signature).map_err(|e| if several { format!("pattern {}: {e}", k + 1) } else { e })?);
    }
    let mut names = Vec::with_capacity(chunks.len());
    for (chunk, prepared) in chunks.iter().zip(prepared) {
        // A single pattern is stored exactly as given.
        names.push(save_prepared(view, if several { chunk } else { text }, prepared)?);
    }
    if reanalyze {
        view.reanalyze();
    }
    Ok(names.join(", "))
}

/// Remove every pattern registered under `name` (or the one record with that id).
pub fn remove_pattern(view: &View, name: &str, reanalyze: bool) -> bool {
    {
        let _guard = lock(&WRITE_LOCK);
        let records = load_records(view);
        let mut kept: Vec<PatternRecord> = records.iter().filter(|r| r.name != name && r.id != name).cloned().collect();
        if kept.len() == records.len() {
            return false;
        }
        prune_targets(view, &target_keys(&kept));
        save_records_raw(view, &mut kept);
        forget_compiled();
    }
    log_info(&format!("removed outlining pattern {name:?}"));
    if reanalyze {
        view.reanalyze();
    }
    true
}

/// Load one or more patterns from a text file.  Patterns are separated by a
/// line containing only `---`; each needs its own `signature:` line.  A
/// pattern that is already saved (written the same way, apart from comments
/// and spacing), or that comes earlier in the file, is skipped.
pub fn load_pattern_file(view: &View, path: &str, reanalyze: bool) -> Result<Vec<String>, String> {
    let content = std::fs::read_to_string(path).map_err(|e| format!("could not read {path}: {e}"))?;
    let mut present = ChunkSet::new(load_records(view).iter().map(PatternRecord::full_text));
    let mut loaded = Vec::new();
    let mut skipped = 0;
    for chunk in split_chunks(&content) {
        if chunk.trim().is_empty() {
            continue;
        }
        if !present.insert(&chunk) {
            skipped += 1;
            continue;
        }
        loaded.push(add_pattern(view, &chunk, None, false)?);
    }
    if skipped > 0 {
        log_info(&format!("{path}: skipped {skipped} pattern(s) already present"));
    }
    if reanalyze && !loaded.is_empty() {
        view.reanalyze();
    }
    Ok(loaded)
}

/// Write the view's saved patterns to a file that [`load_pattern_file`] reads
/// back.  Returns how many patterns were written.
pub fn save_pattern_file(view: &View, path: &str) -> Result<usize, String> {
    let records = load_records(view);
    let texts: Vec<String> = records.iter().map(PatternRecord::full_text).collect();
    std::fs::write(path, join_chunks(&texts)).map_err(|e| format!("could not write {path}: {e}"))?;
    Ok(records.len())
}
