//! The matcher's callbacks, answered by Binary Ninja.
//!
//! One environment serves one activity invocation on one thread.  Symbols,
//! purity, type comparisons and member lookups hold for the view and are
//! memoized for the invocation; definitions, uses and expression types hold
//! for one MLIL function, i.e. one round, and are dropped with it.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use binaryninjacore_sys::*;

use outliner_core::env::{Env, Merge, MergeSource};
use outliner_core::il::{BlockSet, ExprId, Function, InstrSet, TypeId, VarId};
use outliner_core::ops::Op;
use outliner_core::pattern::TypeConstraint;

use crate::ffi::{log_debug, Func, Mlil, TypeRef, View};
use crate::snapshot::bn_var;
use crate::store;
use crate::types::{normalize, TypeTable};

/// An SSA variable: the core's variable and a version.
type SsaVar = (u64, usize);
/// A use query: the definition, the variable, and the blocks kept by a fusion.
type UseKey = (u32, VarId, Option<BlockSet>);
/// A member lookup: the type, the offset, and whether the type is dereferenced.
type MemberKey = (TypeId, i64, bool);

struct Round {
    mlil: Mlil,
    ssa: Option<Mlil>,
    /// (start, end) of the SSA function's blocks, by block index.
    ssa_blocks: Vec<(usize, usize)>,
    defs: HashMap<(u32, VarId), Option<u32>>,
    uses: HashMap<UseKey, Vec<u32>>,
    all_uses: HashMap<(u32, VarId), Option<Vec<u32>>>,
    expr_types: HashMap<u32, Option<TypeId>>,
}

pub struct BnEnv {
    view: View,
    arch: *mut BNArchitecture,
    pub types: RefCell<TypeTable>,
    round: RefCell<Option<Round>>,
    symbols: RefCell<HashMap<u64, Arc<[String]>>>,
    pure: RefCell<HashMap<u64, bool>>,
    type_matches: RefCell<HashMap<(TypeId, String), bool>>,
    members: RefCell<HashMap<MemberKey, Option<(i64, TypeId)>>>,
    /// The global covering an address: its start and type.
    globals: RefCell<HashMap<u64, Option<(u64, TypeId)>>>,
}

impl BnEnv {
    pub fn new(view: View, func: &Func, types: TypeTable) -> BnEnv {
        BnEnv {
            view,
            arch: func.arch(),
            types: RefCell::new(types),
            round: RefCell::new(None),
            symbols: RefCell::new(HashMap::new()),
            pure: RefCell::new(HashMap::new()),
            type_matches: RefCell::new(HashMap::new()),
            members: RefCell::new(HashMap::new()),
            globals: RefCell::new(HashMap::new()),
        }
    }

    /// Forget what was memoized about another MLIL function.
    pub fn begin_round(&self, mlil: Mlil) {
        let ssa = mlil.ssa_form();
        let ssa_blocks = ssa
            .as_ref()
            .map(|s| {
                let mut blocks = s.basic_blocks();
                blocks.sort_by_key(|b| b.index());
                blocks.iter().map(|b| (b.start() as usize, b.end() as usize)).collect()
            })
            .unwrap_or_default();
        *self.round.borrow_mut() = Some(Round {
            mlil,
            ssa,
            ssa_blocks,
            defs: HashMap::new(),
            uses: HashMap::new(),
            all_uses: HashMap::new(),
            expr_types: HashMap::new(),
        });
    }

    /// Gives an address a name the code has no symbol for (a preview's
    /// stand-in call target).
    pub fn name_address(&self, addr: u64, name: &str) {
        let names: Arc<[String]> = vec![name.to_string()].into();
        self.symbols.borrow_mut().insert(addr, names);
    }

    /// The round's MLIL function (the one the snapshot was read from).
    pub fn mlil(&self) -> Option<Mlil> {
        self.round.borrow().as_ref().map(|r| r.mlil.clone())
    }

    fn intern(&self, t: TypeRef) -> TypeId {
        self.types.borrow_mut().intern(t)
    }

    fn type_ref(&self, t: TypeId) -> TypeRef {
        self.types.borrow().get(t).clone()
    }

    fn with_round<R>(&self, f: impl FnOnce(&mut Round) -> R) -> Option<R> {
        self.round.borrow_mut().as_mut().map(f)
    }

    // -- SSA -----------------------------------------------------------------------

    /// The SSA op of an SSA instruction and its raw form.
    fn ssa_instr(ssa: &Mlil, index: usize) -> (Op, BNMediumLevelILInstruction) {
        let raw = ssa.raw_expr(ssa.expr_for_instruction(index));
        (Op::from_u32(raw.operation as u32).unwrap_or(Op::Undef), raw)
    }

    /// The SSA variables an SSA instruction writes.
    fn ssa_vars_written(ssa: &Mlil, index: usize) -> Vec<SsaVar> {
        let (op, raw) = Self::ssa_instr(ssa, index);
        let expr = ssa.expr_for_instruction(index);
        let o = raw.operands;
        match op {
            Op::SetVarSsa | Op::SetVarSsaField | Op::SetVarAliased | Op::SetVarAliasedField | Op::VarPhi => {
                vec![(o[0], o[1] as usize)]
            }
            Op::SetVarSplitSsa => vec![(o[0], o[1] as usize), (o[2], o[3] as usize)],
            Op::CallSsa | Op::CallUntypedSsa | Op::SyscallSsa | Op::SyscallUntypedSsa | Op::TailcallSsa | Op::TailcallUntypedSsa
            | Op::MemoryIntrinsicSsa => Self::ssa_output_vars(ssa, o[0] as usize),
            Op::IntrinsicSsa => pairs(ssa.operand_list(expr, 0)),
            _ => Vec::new(),
        }
    }

    /// The variables an SSA call's output expression writes.  `CALL_OUTPUT_SSA`
    /// lists output expressions (`VAR_OUTPUT_SSA` and its field, aliased and
    /// by-reference forms); `MEMORY_INTRINSIC_OUTPUT_SSA` lists SSA variables.
    fn ssa_output_vars(ssa: &Mlil, output: usize) -> Vec<SsaVar> {
        let raw = ssa.raw_expr(output);
        match Op::from_u32(raw.operation as u32) {
            Some(Op::CallOutputSsa) => {
                ssa.operand_list(output, 1).into_iter().filter_map(|e| Self::ssa_output_var(ssa, e as usize)).collect()
            }
            Some(Op::MemoryIntrinsicOutputSsa) => pairs(ssa.operand_list(output, 1)),
            _ => Vec::new(),
        }
    }

    fn ssa_output_var(ssa: &Mlil, expr: usize) -> Option<SsaVar> {
        let raw = ssa.raw_expr(expr);
        match Op::from_u32(raw.operation as u32)? {
            Op::VarOutputSsa | Op::VarOutputSsaField | Op::VarOutputAliased | Op::VarOutputAliasedField => {
                Some((raw.operands[0], raw.operands[1] as usize))
            }
            Op::ReturnByRef => Self::ssa_output_var(ssa, raw.operands[0] as usize),
            _ => None,
        }
    }

    /// The versions a phi merges.
    fn phi_sources(ssa: &Mlil, index: usize) -> Vec<SsaVar> {
        pairs(ssa.operand_list(ssa.expr_for_instruction(index), 2))
    }

    fn real_uses(
        &self,
        f: &Function,
        ssa: &Mlil,
        var: SsaVar,
        seen: &mut HashSet<SsaVar>,
        kept: Option<&BlockSet>,
        own_block_kept: bool,
        out: &mut Vec<u32>,
    ) {
        if !seen.insert(var) {
            return;
        }
        let variable = crate::ffi::var_from_identifier(var.0);
        for use_index in ssa.ssa_var_uses(&variable, var.1) {
            let (op, _) = Self::ssa_instr(ssa, use_index);
            if op == Op::VarPhi {
                // A definition from outside the kept arm that meets a kept-arm
                // definition at a merge only arrived there through the removed arm.
                if let Some(kept) = kept {
                    if !own_block_kept && self.phi_superseded(f, ssa, use_index, var, kept) {
                        continue;
                    }
                }
                for produced in Self::ssa_vars_written(ssa, use_index) {
                    self.real_uses(f, ssa, produced, seen, kept, own_block_kept, out);
                }
            } else {
                out.push(ssa.non_ssa_instruction_index(use_index) as u32);
            }
        }
    }

    fn phi_superseded(&self, f: &Function, ssa: &Mlil, phi: usize, var: SsaVar, kept: &BlockSet) -> bool {
        for operand in Self::phi_sources(ssa, phi) {
            if operand == var {
                continue;
            }
            let variable = crate::ffi::var_from_identifier(operand.0);
            let Some(definition) = ssa.ssa_var_definition(&variable, operand.1) else { continue };
            let index = ssa.non_ssa_instruction_index(definition) as u32;
            if (index as usize) < f.len() && kept.contains(f.block_id_of(index).0 as usize) {
                return true;
            }
        }
        false
    }

    fn compute_uses(&self, f: &Function, round: &Round, def_index: u32, var: VarId, kept: Option<&BlockSet>) -> Option<Vec<u32>> {
        let ssa = round.ssa.as_ref()?;
        let ssa_index = round.mlil.ssa_instruction_index(def_index as usize);
        if ssa_index >= ssa.instruction_count() {
            return None;
        }
        let own_block_kept = kept.is_some_and(|k| k.contains(f.block_id_of(def_index).0 as usize));
        let wanted = crate::ffi::var_identifier(&bn_var(f.var(var)));
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        for written in Self::ssa_vars_written(ssa, ssa_index) {
            if written.0 != wanted {
                continue;
            }
            self.real_uses(f, ssa, written, &mut seen, kept, own_block_kept, &mut out);
        }
        Some(out)
    }

    fn compute_definition(&self, f: &Function, round: &Round, use_index: u32, var: VarId) -> Option<u32> {
        let ssa = round.ssa.as_ref()?;
        let variable = bn_var(f.var(var));
        let version = round.mlil.ssa_var_version_at(&variable, use_index as usize);
        let definition = ssa.ssa_var_definition(&variable, version)?;
        let (op, _) = Self::ssa_instr(ssa, definition);
        if !matches!(op, Op::SetVarSsa | Op::CallSsa | Op::SetVarSsaField) {
            return None;
        }
        let index = ssa.non_ssa_instruction_index(definition) as u32;
        if index as usize >= f.len() {
            return None;
        }
        let instr = f.instr(index);
        match f.op(instr) {
            Op::SetVar | Op::SetVarField if f.var_operand(instr, 0) == Some(var) => Some(index),
            Op::Call if f.call_outputs(instr).as_slice() == [var] => Some(index),
            _ => None,
        }
    }

    // -- types ---------------------------------------------------------------------

    fn resolve_named(&self, mut t: TypeRef) -> Option<TypeRef> {
        let mut seen = 0;
        while t.class() == BNTypeClass::NamedTypeReferenceClass && seen < 8 {
            t = t.resolve_named(&self.view)?;
            seen += 1;
        }
        Some(t)
    }

    fn type_width(&self, t: &TypeRef) -> u64 {
        let width = t.width();
        if width != 0 {
            return width;
        }
        self.resolve_named(t.clone()).map_or(0, |r| r.width())
    }

    /// The data variable whose bytes include `addr`: the one starting there,
    /// else the last one starting before it, when it is wide enough.
    fn compute_data_var(&self, addr: u64) -> Option<(u64, TypeId)> {
        let covers = |start: u64, t: &TypeRef| start <= addr && addr < start.saturating_add(self.type_width(t).max(1));
        if let Some((start, t)) = self.view.data_var_at(addr) {
            if covers(start, &t) {
                return Some((start, self.intern(t)));
            }
        }
        let previous = self.view.previous_data_var_start(addr);
        if previous < addr {
            if let Some((start, t)) = self.view.data_var_at(previous) {
                if covers(start, &t) {
                    return Some((start, self.intern(t)));
                }
            }
        }
        None
    }

    fn compute_member(&self, t: TypeId, offset: i64, deref: bool) -> Option<(i64, TypeId)> {
        let mut t = self.resolve_named(self.type_ref(t))?; // a typedef may name the pointer itself
        if deref {
            if t.class() != BNTypeClass::PointerTypeClass {
                return None; // references are pointers here
            }
            t = self.resolve_named(t.child()?)?;
        }
        if t.class() != BNTypeClass::StructureTypeClass {
            return None;
        }
        let members = t.members();
        for (k, (start, member)) in members.iter().enumerate() {
            let start = *start as i64;
            // A member typed by name (`std::__1::string`) may report no width of
            // its own: take the referenced type's, else the next member's start.
            let width = self.type_width(member) as i64;
            let end = if width != 0 {
                start + width
            } else if k + 1 < members.len() {
                members[k + 1].0 as i64
            } else if t.width() != 0 {
                t.width() as i64
            } else {
                start + 1
            };
            if start <= offset && offset < end {
                return Some((start, self.intern(member.clone())));
            }
        }
        None
    }

    fn compute_types_match(&self, actual: TypeId, constraint: &TypeConstraint) -> bool {
        let actual_text = self.types.borrow_mut().text(actual).to_string();
        if constraint.is_regex() {
            return constraint.regex_matches(&actual_text);
        }
        if let Some(expected) = store::parse_type_cached(&self.view, &constraint.text) {
            if self.type_ref(actual) == expected {
                return true;
            }
            if normalize(&actual_text) == normalize(&expected.text()) {
                return true;
            }
        }
        normalize(&actual_text) == normalize(&constraint.text)
    }

    fn is_pure_target(&self, addr: u64) -> bool {
        let ty = self.view.data_var_type_at(addr).or_else(|| self.view.function_at(addr).and_then(|f| f.ty()));
        ty.is_some_and(|t| t.is_pure())
    }
}

/// (variable, version) pairs of a raw SSA variable list.
fn pairs(list: Vec<u64>) -> Vec<SsaVar> {
    list.chunks_exact(2).map(|c| (c[0], c[1] as usize)).collect()
}

impl Env for BnEnv {
    fn type_of_expr(&self, f: &Function, e: ExprId) -> Option<TypeId> {
        if f.op(e) == Op::Var {
            return f.var_of(e).and_then(|v| f.var(v).ty);
        }
        let source = f.expr(e).source;
        let cached = self.round.borrow().as_ref().and_then(|r| r.expr_types.get(&source).copied());
        if let Some(t) = cached {
            return t;
        }
        let t = self.mlil()?.expr_type(source as usize).map(|t| self.intern(t));
        self.with_round(|r| r.expr_types.insert(source, t));
        t
    }

    fn type_of_var(&self, f: &Function, v: VarId) -> Option<TypeId> {
        f.var(v).ty
    }

    fn pointer_to(&self, t: TypeId) -> Option<TypeId> {
        self.type_ref(t).pointer_to(self.arch).map(|p| self.intern(p))
    }

    fn types_match(&self, actual: TypeId, constraint: &TypeConstraint) -> bool {
        let key = (actual, constraint.text.clone());
        if let Some(answer) = self.type_matches.borrow().get(&key) {
            return *answer;
        }
        let answer = self.compute_types_match(actual, constraint);
        self.type_matches.borrow_mut().insert(key, answer);
        answer
    }

    fn type_text(&self, t: TypeId) -> String {
        self.types.borrow_mut().text(t).to_string()
    }

    fn type_spelling(&self, t: TypeId) -> String {
        self.types.borrow().get(t).spelling()
    }

    fn symbol_names_at(&self, addr: u64) -> Arc<[String]> {
        if let Some(names) = self.symbols.borrow().get(&addr) {
            return names.clone();
        }
        let mut names: Vec<String> = Vec::new();
        for symbol in self.view.symbols_at(addr) {
            names.extend([symbol.raw_name(), symbol.short_name(), symbol.full_name()]);
        }
        if let Some(func) = self.view.function_at(addr) {
            names.push(func.name());
        }
        names.sort();
        names.dedup();
        let names: Arc<[String]> = names.into();
        self.symbols.borrow_mut().insert(addr, names.clone());
        names
    }

    fn definition_of(&self, f: &Function, use_index: u32, var: VarId) -> Option<u32> {
        let key = (use_index, var);
        let mut guard = self.round.borrow_mut();
        let round = guard.as_mut()?;
        if let Some(cached) = round.defs.get(&key) {
            return *cached;
        }
        let result = self.compute_definition(f, round, use_index, var);
        round.defs.insert(key, result);
        result
    }

    fn uses_of(&self, f: &Function, def_index: u32, var: VarId, kept_blocks: Option<&BlockSet>) -> Vec<u32> {
        let key = (def_index, var, kept_blocks.cloned());
        let mut guard = self.round.borrow_mut();
        let Some(round) = guard.as_mut() else { return vec![u32::MAX] };
        if let Some(cached) = round.uses.get(&key) {
            return cached.clone();
        }
        // Unknown: report a use nobody can account for.
        let result = self.compute_uses(f, round, def_index, var, kept_blocks).unwrap_or_else(|| vec![u32::MAX]);
        round.uses.insert(key, result.clone());
        result
    }

    fn merges_of(&self, f: &Function, def_index: u32, var: VarId, at_index: u32) -> Option<Vec<Merge>> {
        let guard = self.round.borrow();
        let round = guard.as_ref()?;
        let ssa = round.ssa.as_ref()?;
        let variable = bn_var(f.var(var));
        let wanted = crate::ffi::var_identifier(&variable);
        let live_version = round.mlil.ssa_var_version_at(&variable, at_index as usize);
        let ssa_index = round.mlil.ssa_instruction_index(def_index as usize);
        if ssa_index >= ssa.instruction_count() {
            return None;
        }
        let classify = |operand: SsaVar| -> MergeSource {
            if operand.1 == live_version {
                return MergeSource::Live;
            }
            let v = crate::ffi::var_from_identifier(operand.0);
            match ssa.ssa_var_definition(&v, operand.1) {
                None => MergeSource::Unknown,
                Some(d) if Self::ssa_instr(ssa, d).0 == Op::VarPhi => MergeSource::Unknown,
                Some(d) => MergeSource::Def(ssa.non_ssa_instruction_index(d) as u32),
            }
        };
        let block_start = |phi: usize| -> u32 {
            let (bi, &(start, end)) =
                round.ssa_blocks.iter().enumerate().find(|(_, (s, e))| *s <= phi && phi < *e).unwrap_or((0, &(0, 0)));
            for k in start..end {
                if !matches!(Self::ssa_instr(ssa, k).0, Op::VarPhi | Op::MemPhi) {
                    let index = ssa.non_ssa_instruction_index(k) as u32;
                    if (index as usize) < f.len() {
                        return f.block_of(index).start;
                    }
                }
            }
            f.blocks.get(bi).map_or(0, |b| b.start)
        };
        let mut out: Vec<Merge> = Vec::new();
        let mut chain: HashSet<SsaVar> = HashSet::new();
        // Record the phis below `var` that lead to a real use; true if any use exists.
        fn walk(
            ssa: &Mlil,
            var: SsaVar,
            chain: &mut HashSet<SsaVar>,
            out: &mut Vec<Merge>,
            classify: &dyn Fn(SsaVar) -> MergeSource,
            block_start: &dyn Fn(usize) -> u32,
        ) -> bool {
            if !chain.insert(var) {
                return false;
            }
            let mut found = false;
            let variable = crate::ffi::var_from_identifier(var.0);
            for use_index in ssa.ssa_var_uses(&variable, var.1) {
                if BnEnv::ssa_instr(ssa, use_index).0 != Op::VarPhi {
                    found = true;
                    continue;
                }
                let others: Vec<MergeSource> =
                    BnEnv::phi_sources(ssa, use_index).into_iter().filter(|s| !chain.contains(s)).map(classify).collect();
                let produced = BnEnv::ssa_vars_written(ssa, use_index);
                if produced.into_iter().any(|p| walk(ssa, p, chain, out, classify, block_start)) {
                    out.push(Merge { block_start: block_start(use_index), others });
                    found = true;
                }
            }
            found
        }
        for written in Self::ssa_vars_written(ssa, ssa_index) {
            if written.0 == wanted {
                walk(ssa, written, &mut chain, &mut out, &classify, &block_start);
            }
        }
        Some(out)
    }

    fn uses_outside(&self, f: &Function, instr_index: u32, region: &InstrSet, var: VarId) -> bool {
        let key = (instr_index, var);
        let mut guard = self.round.borrow_mut();
        let Some(round) = guard.as_mut() else { return true };
        if !round.all_uses.contains_key(&key) {
            let uses = self.compute_uses(f, round, instr_index, var, None);
            round.all_uses.insert(key, uses);
        }
        match &round.all_uses[&key] {
            None => true, // unknown: treat the value as live
            Some(uses) => uses.iter().any(|u| {
                let outside = !region.contains(*u as usize);
                if outside {
                    log_debug(&format!("{} defined at {instr_index} is still used at {u}", f.var_name(var)));
                }
                outside
            }),
        }
    }

    fn read_bytes(&self, addr: u64, size: usize) -> Option<Vec<u8>> {
        self.view.read(addr, size)
    }

    fn find_bytes(&self, data: &[u8]) -> Option<u64> {
        self.view.find_next_data(self.view.start(), data)
    }

    fn member_containing(&self, t: TypeId, offset: i64, deref: bool) -> Option<(i64, TypeId)> {
        let key = (t, offset, deref);
        if let Some(found) = self.members.borrow().get(&key) {
            return *found;
        }
        let found = self.compute_member(t, offset, deref);
        self.members.borrow_mut().insert(key, found);
        found
    }

    fn data_var_containing(&self, addr: u64) -> Option<(u64, TypeId)> {
        if let Some(found) = self.globals.borrow().get(&addr) {
            return *found;
        }
        let found = self.compute_data_var(addr);
        self.globals.borrow_mut().insert(addr, found);
        found
    }

    fn is_pure_call(&self, f: &Function, instr: u32) -> bool {
        let call = f.instr(instr);
        let Some(dest) = f.call_dest(call) else { return false };
        if !matches!(f.op(dest), Op::ConstPtr | Op::Const | Op::Import) {
            return false;
        }
        let Some(addr) = f.int_operand(dest, 0) else { return false };
        let addr = addr as u64;
        if let Some(answer) = self.pure.borrow().get(&addr) {
            return *answer;
        }
        let answer = self.is_pure_target(addr);
        self.pure.borrow_mut().insert(addr, answer);
        answer
    }
}

