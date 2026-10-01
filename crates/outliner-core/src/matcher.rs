//! Match parsed patterns against MLIL functions.
//!
//! Matching is tolerant of what optimizers do to inlined code:
//!
//! * **Interleaving**: within the entry block, pattern statements match a
//!   subsequence of the instructions.  Instructions in between are *kept* (they
//!   stay in the output, ahead of the call) as long as they do not interfere
//!   with the pattern: they must be side-effect free, may not write anything
//!   the pattern reads and may not read anything the pattern writes.
//! * **Hoisting**: when the pattern expects an expression but the code has a
//!   variable, the matcher follows the variable's (unique) definition and
//!   matches the expression there.  Such definitions are deleted together with
//!   the region when nothing else uses their value; otherwise they are left in
//!   place.
//! * **Spelling**: user-declared rewrite rules (`rewrite: lhs => rhs [when cond]`)
//!   let one pattern match every way a compiler spells the same computation.
//!   When structural matching of an expression fails, each rule whose left side
//!   matches the code is applied and matching continues on the rewritten form.
//!   A `when` condition must be implied by an enclosing branch of the pattern.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};

use fixedbitset::FixedBitSet;
use smallvec::SmallVec;

use crate::binding::{Binding, MemberBase, MemberKind, MemberRef};
use crate::env::Env;
use crate::hybrid::{
    complement_of, const_equal, hybrid_equal, instantiate, normalize_condition, Fail, HOp, MResult, Node,
};
use crate::il::{BlockId, BlockSet, ExprId, Function, InstrSet, Operand, TypeId, VarId};
use crate::ops::Op;
use crate::pattern::{
    image_store, negate, Block as PBlock, CallExpr, Dest, Expr, ImageStore, IntArg, LabelId, LenArg, Pattern, PhId,
    Rule, Stmt, SymbolRef, TypeConstraint, RET,
};

pub const MAX_RULE_DEPTH: u32 = 6;

/// A set of variables of one function.
pub type VarSet = FixedBitSet;

/// A set of MLIL operations.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct OpSet([u64; 3]);

impl OpSet {
    pub fn insert(&mut self, op: Op) {
        let v = op as usize;
        self.0[v / 64] |= 1 << (v % 64);
    }

    pub fn contains(&self, op: Op) -> bool {
        let v = op as usize;
        self.0[v / 64] & (1 << (v % 64)) != 0
    }

    pub fn of(ops: &[Op]) -> OpSet {
        let mut s = OpSet::default();
        for op in ops {
            s.insert(*op);
        }
        s
    }
}

/// A branch fact: a normalized condition and whether it holds.
pub type Fact = (Node, bool);

type MemoKey = (usize, i32, Node);
type MemoEntry = Option<(Node, Vec<(u32, VarId)>)>;

/// One round of matching over one function: the function, the host's
/// environment, and what the round memoizes across matching attempts.
pub struct Round<'a> {
    pub f: &'a Function,
    pub env: &'a dyn Env,
    memo: RefCell<HashMap<MemoKey, MemoEntry>>,
}

impl<'a> Round<'a> {
    pub fn new(f: &'a Function, env: &'a dyn Env) -> Round<'a> {
        Round { f, env, memo: RefCell::new(HashMap::new()) }
    }

    /// How many rule applications the round has memoized: (rewrites kept, failures kept).
    pub fn memo_counts(&self) -> (usize, usize) {
        let memo = self.memo.borrow();
        let kept = memo.values().filter(|v| v.is_some()).count();
        (kept, memo.len() - kept)
    }
}

/// A successful match of a pattern's statements.
#[derive(Clone, Debug)]
pub struct Match {
    /// Index of the pattern in the list the finder was given.
    pub pattern: usize,
    /// First matched statement (source location of the call).
    pub entry_index: u32,
    /// Instruction whose slot receives the call.
    pub call_index: u32,
    /// Every instruction index replaced by the call.
    pub deleted: InstrSet,
    /// Starts of the blocks containing deleted instructions.
    pub region_blocks: Vec<u32>,
    /// Starts of the blocks removed entirely.
    pub internal_blocks: Vec<u32>,
    /// Where control continues after the call.
    pub exit_index: Option<u32>,
    /// True if the call must be followed by a goto to `exit_index`.
    pub exit_goto: bool,
    pub bindings: Vec<Option<Binding>>,
    pub labels: Vec<Option<u32>>,
    /// Starts of the blocks holding matched statements (not followed definitions).
    pub own_blocks: Vec<u32>,
    /// Instructions inside the span left in place.
    pub kept: Vec<u32>,
    /// Followed definitions: (index, variable).
    pub chased: Vec<(u32, VarId)>,
    pub ret_size: u16,
    /// Receives the call when the pattern has a `result:` line (set by the planner).
    pub result_var: Option<VarId>,
    /// Where the exit branch (`branch:`) leaves to.
    pub branch_target: Option<u32>,
}

impl Match {
    pub fn binding(&self, id: PhId) -> Option<&Binding> {
        self.bindings.get(id.0 as usize).and_then(|b| b.as_ref())
    }

    /// The variable that receives the result, when `$ret` is bound to one.
    pub fn ret_var(&self, f: &Function) -> Option<VarId> {
        self.binding(RET).and_then(|b| b.bound_var(f))
    }

    pub fn deleted_sorted(&self) -> Vec<u32> {
        self.deleted.ones().map(|i| i as u32).collect()
    }

    /// The variables the call's arguments read (those passed by address excepted).
    pub fn arg_vars(&self, pattern: &Pattern, f: &Function) -> Vec<VarId> {
        let by_reference = pattern.reference_placeholders();
        let mut out: Vec<VarId> = Vec::new();
        for name in pattern.argument_placeholders() {
            if by_reference.contains(name) {
                continue;
            }
            if let Some(b) = self.binding(name) {
                for v in b.reads(f) {
                    if !out.contains(&v) {
                        out.push(v);
                    }
                }
            }
        }
        out
    }
}

/// A pointer value resolved through copies and address arithmetic.
#[derive(Clone, Debug)]
pub(crate) enum Pointee {
    /// Variable `v`'s value.
    Ptr(VarId),
    /// The address of `v`.
    Addr(VarId),
    /// Any other expression.
    Expr(Node),
}

impl Pointee {
    fn kind(&self) -> MemberKind {
        match self {
            Pointee::Ptr(_) => MemberKind::Ptr,
            Pointee::Addr(_) => MemberKind::Addr,
            Pointee::Expr(_) => MemberKind::Expr,
        }
    }

    fn base(&self) -> Option<MemberBase> {
        match self {
            Pointee::Ptr(v) | Pointee::Addr(v) => Some(MemberBase::Var(*v)),
            Pointee::Expr(Node::Expr(e)) | Pointee::Expr(Node::Sited(e, _)) => Some(MemberBase::Expr(*e)),
            Pointee::Expr(_) => None,
        }
    }
}

/// Rolled-back state of an attempt.
struct Snapshot {
    bindings: Vec<Option<Binding>>,
    bind_site: Vec<i32>,
    labels: Vec<Option<u32>>,
    matched_len: usize,
    chased_len: usize,
    ret_size: u16,
    facts: Vec<Fact>,
    block_facts: Vec<Vec<Fact>>,
    clobbered_len: usize,
    absorbed_len: usize,
}

enum BindAction {
    Var(VarId),
    Addr(VarId),
    ExprCopies(ExprId),
}

/// Which kind of value a placeholder is being bound to, for its type check.
enum Typed<'m> {
    Var(VarId),
    Addr(VarId),
    Expr(ExprId),
    Member(&'m MemberRef),
    /// The object at a fixed address, or (`object` false) a pointer to it.
    Global { addr: u64, object: bool },
}

/// The matcher's state for one attempt.
pub(crate) struct State<'a> {
    pub round: &'a Round<'a>,
    pub f: &'a Function,
    pub env: &'a dyn Env,
    pub pattern: &'a Pattern,
    types: &'a [Option<TypeConstraint>],
    pub extra_deleted: &'a InstrSet,
    pub extra_live: &'a VarSet,
    pub rules: &'a [Rule],
    pub facts: Vec<Fact>,
    /// Facts per pattern block: slot 0 is the entry, slot `l + 1` the block labeled `l`.
    block_facts: Vec<Vec<Fact>>,
    pub check_types: bool,
    rule_depth: u32,
    pub bindings: Vec<Option<Binding>>,
    /// Instruction where each binding was established (-1: none).
    pub bind_site: Vec<i32>,
    pub labels: Vec<Option<u32>>,
    /// Instructions matched by pattern statements.
    matched: InstrSet,
    matched_stack: Vec<u32>,
    /// Definitions followed: (index, variable).
    pub chased: Vec<(u32, VarId)>,
    chased_set: InstrSet,
    internal_blocks: Vec<BlockId>,
    exit_index: Option<u32>,
    exit_goto: bool,
    ret_size: u16,
    /// Instruction whose operands are being matched (-1: none).
    pub use_index: i32,
    /// > 0 while matching a load/store address.
    in_address: u32,
    /// Call outputs matched by a trailing `...`: not needed.
    pub clobbered: Vec<VarId>,
    /// Definitions that may not be followed (being rewritten).
    pub blocked_defs: Option<&'a InstrSet>,
    /// Unmatched pure assignments inside arm blocks, gone with the region.
    absorbed: Vec<u32>,
    absorbed_set: InstrSet,
    /// True while matching a non-entry block.
    absorbable: bool,
    /// Where matching got to, kept when explaining a failure.
    pub trace: Option<Trace>,
    /// The pattern block being matched (an index into the pattern's blocks).
    current_block: usize,
    current_stmt: usize,
    /// A chase was refused because of this state, not the code.
    pub refused_chase: bool,
    entry_first: Option<u32>,
    entry_last: Option<u32>,
}

impl<'a> State<'a> {
    pub fn new(
        round: &'a Round<'a>,
        pattern: &'a Pattern,
        extra_deleted: &'a InstrSet,
        extra_live: &'a VarSet,
        rules: &'a [Rule],
        facts: Vec<Fact>,
    ) -> State<'a> {
        let f = round.f;
        let count = pattern.ph_count();
        State {
            round,
            f,
            env: round.env,
            pattern,
            types: &pattern.types,
            extra_deleted,
            extra_live,
            rules,
            facts,
            block_facts: vec![Vec::new(); pattern.labels.len() + 1],
            check_types: true,
            rule_depth: 0,
            bindings: vec![None; count],
            bind_site: vec![-1; count],
            labels: vec![None; pattern.labels.len()],
            matched: f.instr_set(),
            matched_stack: Vec::new(),
            chased: Vec::new(),
            chased_set: f.instr_set(),
            internal_blocks: Vec::new(),
            exit_index: None,
            exit_goto: false,
            ret_size: 0,
            use_index: -1,
            in_address: 0,
            clobbered: Vec::new(),
            blocked_defs: None,
            absorbed: Vec::new(),
            absorbed_set: f.instr_set(),
            absorbable: false,
            trace: None,
            current_block: 0,
            current_stmt: 0,
            refused_chase: false,
            entry_first: None,
            entry_last: None,
        }
    }

    /// A state for matching one rewrite rule's left side: the rule's own
    /// placeholders, no type checks, no further rules.
    fn for_rule(&self, rule: &'a Rule) -> State<'a> {
        let count = rule.names.len();
        State {
            round: self.round,
            f: self.f,
            env: self.env,
            pattern: self.pattern,
            types: &[],
            extra_deleted: self.extra_deleted,
            extra_live: self.extra_live,
            rules: &[],
            facts: self.facts.clone(),
            block_facts: Vec::new(),
            check_types: false,
            rule_depth: self.rule_depth,
            bindings: vec![None; count],
            bind_site: vec![-1; count],
            labels: Vec::new(),
            matched: self.f.instr_set(),
            matched_stack: Vec::new(),
            chased: Vec::new(),
            chased_set: self.f.instr_set(),
            internal_blocks: Vec::new(),
            exit_index: None,
            exit_goto: false,
            ret_size: 0,
            use_index: self.use_index,
            in_address: 0,
            clobbered: Vec::new(),
            blocked_defs: self.blocked_defs,
            absorbed: Vec::new(),
            absorbed_set: self.f.instr_set(),
            absorbable: false,
            trace: None,
            current_block: 0,
            current_stmt: 0,
            refused_chase: false,
            entry_first: None,
            entry_last: None,
        }
    }

    pub fn set_bindings(&mut self, bindings: Vec<Option<Binding>>, sites: Vec<i32>) {
        self.bindings = bindings;
        self.bind_site = sites;
    }

    // -- sets ----------------------------------------------------------------
    fn is_matched(&self, i: u32) -> bool {
        self.matched.contains(i as usize)
    }

    fn set_matched(&mut self, i: u32) {
        if !self.matched.contains(i as usize) {
            self.matched.insert(i as usize);
            self.matched_stack.push(i);
        }
    }

    fn unmatch(&mut self, i: u32) {
        if self.matched.contains(i as usize) {
            self.matched.set(i as usize, false);
            if let Some(pos) = self.matched_stack.iter().rposition(|x| *x == i) {
                self.matched_stack.remove(pos);
            }
        }
    }

    fn is_absorbed(&self, i: u32) -> bool {
        self.absorbed_set.contains(i as usize)
    }

    fn is_blocked(&self, i: u32) -> bool {
        self.blocked_defs.map(|b| b.contains(i as usize)).unwrap_or(false)
    }

    fn is_extra_deleted(&self, i: u32) -> bool {
        self.extra_deleted.contains(i as usize)
    }

    pub fn add_chased(&mut self, index: u32, var: VarId) {
        if !self.chased_set.contains(index as usize) {
            self.chased_set.insert(index as usize);
            self.chased.push((index, var));
        }
    }

    // -- rollback ---------------------------------------------------------------
    fn snapshot(&self) -> Snapshot {
        Snapshot {
            bindings: self.bindings.clone(),
            bind_site: self.bind_site.clone(),
            labels: self.labels.clone(),
            matched_len: self.matched_stack.len(),
            chased_len: self.chased.len(),
            ret_size: self.ret_size,
            facts: self.facts.clone(),
            block_facts: self.block_facts.clone(),
            clobbered_len: self.clobbered.len(),
            absorbed_len: self.absorbed.len(),
        }
    }

    fn restore(&mut self, snap: Snapshot) {
        self.bindings = snap.bindings;
        self.bind_site = snap.bind_site;
        self.labels = snap.labels;
        while self.matched_stack.len() > snap.matched_len {
            let i = self.matched_stack.pop().unwrap();
            self.matched.set(i as usize, false);
        }
        while self.chased.len() > snap.chased_len {
            let (i, _) = self.chased.pop().unwrap();
            self.chased_set.set(i as usize, false);
        }
        self.ret_size = snap.ret_size;
        self.facts = snap.facts;
        self.block_facts = snap.block_facts;
        self.clobbered.truncate(snap.clobbered_len);
        while self.absorbed.len() > snap.absorbed_len {
            let i = self.absorbed.pop().unwrap();
            self.absorbed_set.set(i as usize, false);
        }
    }

    // -- bindings ---------------------------------------------------------------
    fn binding(&self, name: PhId) -> Option<&Binding> {
        self.bindings[name.0 as usize].as_ref()
    }

    fn set_binding(&mut self, name: PhId, b: Binding) {
        self.bindings[name.0 as usize] = Some(b);
        self.bind_site[name.0 as usize] = self.use_index;
    }

    fn check_type(&mut self, name: PhId, value: Typed) -> MResult<()> {
        if !self.check_types {
            return Ok(());
        }
        let Some(constraint) = self.types.get(name.0 as usize).and_then(|t| t.as_ref()) else {
            return Ok(());
        };
        // Every type the value may be read as; a global's address is that of
        // each object starting there (the global, its first member, ...).
        let candidates: SmallVec<[TypeId; 4]> = match value {
            Typed::Var(v) => self.env.type_of_var(self.f, v).into_iter().collect(),
            Typed::Addr(v) => self.env.type_of_var(self.f, v).and_then(|t| self.env.pointer_to(t)).into_iter().collect(),
            Typed::Member(m) => {
                if m.kind == MemberKind::Var {
                    m.ty.into_iter().collect()
                } else {
                    m.ty.and_then(|t| self.env.pointer_to(t)).into_iter().collect()
                }
            }
            Typed::Expr(e) => self.env.type_of_expr(self.f, e).into_iter().collect(),
            Typed::Global { addr, object } => self
                .global_types(addr)
                .into_iter()
                .filter_map(|t| if object { Some(t) } else { self.env.pointer_to(t) })
                .collect(),
        };
        if candidates.iter().any(|t| self.env.types_match(*t, constraint)) {
            return Ok(());
        }
        let have = candidates.first().map(|t| self.env.type_text(*t)).unwrap_or_else(|| "no type".to_string());
        let (ph, want) = (self.pattern.ph_name(name).to_string(), constraint.text.clone());
        Err(self.why(|| format!("${ph} is {have}, the constraint wants {want}")))
    }

    /// Whether the placeholder carries a type constraint.
    fn typed(&self, name: PhId) -> bool {
        self.types.get(name.0 as usize).is_some_and(|t| t.is_some())
    }

    /// The types of the objects that start at `addr`, outermost first: the
    /// global there, then its member at offset 0, and so on; inside a global,
    /// the members that start exactly at `addr`.
    fn global_types(&self, addr: u64) -> SmallVec<[TypeId; 4]> {
        let mut out = SmallVec::new();
        let Some((start, mut t)) = self.env.data_var_containing(addr) else { return out };
        let Some(mut offset) = addr.checked_sub(start).map(|o| o as i64) else { return out };
        for _ in 0..8 {
            if offset == 0 {
                out.push(t);
            }
            match self.env.member_containing(t, offset, false) {
                Some((m, mt)) if m <= offset && !(m == 0 && mt == t) => {
                    offset -= m;
                    t = mt;
                }
                _ => break,
            }
        }
        out
    }

    /// The objects around `at`, outermost first: the global holding it, then
    /// the member of it holding `at`, and so on; their addresses.
    fn global_objects_around(&self, at: u64) -> SmallVec<[u64; 4]> {
        let mut out = SmallVec::new();
        let Some((mut start, mut t)) = self.env.data_var_containing(at) else { return out };
        if at < start {
            return out;
        }
        for _ in 0..8 {
            out.push(start);
            match self.env.member_containing(t, (at - start) as i64, false) {
                Some((m, mt)) if m >= 0 && !(m == 0 && mt == t) => {
                    start += m as u64;
                    t = mt;
                }
                _ => break,
            }
        }
        out
    }

    /// Bind a placeholder to the object at `addr` (see [`Binding::Global`]), or
    /// check it against what the placeholder already stands for: the same
    /// global, or the code's own spelling of its address.
    fn bind_global(&mut self, name: PhId, addr: u64, object: bool) -> MResult<()> {
        match self.binding(name) {
            None => {
                self.check_type(name, Typed::Global { addr, object })?;
                self.set_binding(name, Binding::Global { addr, object });
                Ok(())
            }
            Some(Binding::Global { addr: a, object: o }) if *a == addr && *o == object => Ok(()),
            Some(Binding::Expr { expr, .. }) if !object && self.f.const_value(*expr) == Some(addr as i64) => Ok(()),
            _ => {
                let ph = self.pattern.ph_name(name).to_string();
                Err(self.why(|| format!("${ph} stands for something else elsewhere, the global at {addr:#x} here")))
            }
        }
    }

    fn bind_var(&mut self, name: PhId, var: VarId) -> MResult<()> {
        match self.binding(name) {
            None => {
                self.check_type(name, Typed::Var(var))?;
                self.set_binding(name, Binding::Var(var));
                Ok(())
            }
            Some(Binding::Var(v)) => {
                if *v == var {
                    Ok(())
                } else {
                    let (ph, have, here) = (self.pattern.ph_name(name).to_string(), self.f.var_name(*v).to_string(), self.f.var_name(var).to_string());
                    Err(self.why(|| format!("${ph} is {have} elsewhere, {here} here")))
                }
            }
            Some(Binding::Expr { expr, .. }) => {
                if self.f.var_of(*expr) == Some(var) {
                    Ok(())
                } else {
                    let (ph, here) = (self.pattern.ph_name(name).to_string(), self.f.var_name(var).to_string());
                    Err(self.why(|| format!("${ph} stands for an expression elsewhere, {here} here")))
                }
            }
            _ => {
                let (ph, here) = (self.pattern.ph_name(name).to_string(), self.f.var_name(var).to_string());
                Err(self.why(|| format!("${ph} cannot stand for {here} as well")))
            }
        }
    }

    fn bind_expr(&mut self, name: PhId, expr: ExprId) -> MResult<()> {
        let address = self.in_address > 0;
        match self.binding(name) {
            None => {
                self.check_type(name, Typed::Expr(expr))?;
                self.set_binding(name, Binding::Expr { expr, address });
                Ok(())
            }
            Some(Binding::Expr { expr: existing, address: ea }) => {
                let (existing, ea) = (*existing, *ea);
                if !self.f.expr_equal(existing, expr, ea || address) {
                    return Err(Fail);
                }
                if address && !ea {
                    self.bindings[name.0 as usize] = Some(Binding::Expr { expr: existing, address: true });
                }
                Ok(())
            }
            Some(Binding::Var(v)) => {
                if self.f.var_of(expr) == Some(*v) {
                    Ok(())
                } else {
                    Err(Fail)
                }
            }
            Some(Binding::Global { addr, object: false }) => {
                // a pointer to a global facing the code's spelling of its address
                if self.f.const_value(expr) == Some(*addr as i64) {
                    Ok(())
                } else {
                    Err(Fail)
                }
            }
            Some(b @ (Binding::Int { .. } | Binding::Bytes { .. })) => {
                // A constant the matcher computed (a byte image's length) facing the code's spelling of it.
                let value = b.const_value(self.f);
                if value.is_some() && self.f.const_value(expr).map(|v| v as i128) == value {
                    Ok(())
                } else {
                    Err(Fail)
                }
            }
            _ => Err(Fail),
        }
    }

    fn bind_int(&mut self, name: PhId, value: i128) -> MResult<()> {
        match self.binding(name) {
            None => {
                self.set_binding(name, Binding::Int { value, origin: None });
                Ok(())
            }
            Some(b @ (Binding::Int { .. } | Binding::Bytes { .. })) => {
                if b.const_value(self.f) == Some(value) {
                    Ok(())
                } else {
                    Err(Fail)
                }
            }
            Some(Binding::Expr { expr, .. }) => {
                if self.f.const_value(*expr).map(|v| v as i128) == Some(value) {
                    Ok(())
                } else {
                    Err(Fail)
                }
            }
            _ => Err(Fail),
        }
    }

    /// Bind a placeholder to the address of a variable (`&s`), which is what
    /// the pattern's pointer is when the code holds the object itself.
    fn bind_addr(&mut self, name: PhId, var: VarId) -> MResult<()> {
        match self.binding(name) {
            None => {
                self.check_type(name, Typed::Addr(var))?;
                self.set_binding(name, Binding::Addr(var));
                Ok(())
            }
            Some(Binding::Addr(v)) if *v == var => Ok(()),
            _ => Err(Fail),
        }
    }

    /// A variable read where the placeholder already stands for an address:
    /// it must hold that address, i.e. be defined as `var = &s`.
    fn bind_addr_copy(&mut self, name: PhId, var: VarId) -> MResult<()> {
        let Some(Binding::Addr(target)) = self.binding(name).cloned() else { return Err(Fail) };
        if self.use_index < 0 {
            return Err(Fail);
        }
        let def = self.env.definition_of(self.f, self.use_index as u32, var).ok_or(Fail)?;
        if self.is_extra_deleted(def) || self.is_blocked(def) {
            return Err(Fail);
        }
        let definition = self.f.instr(def);
        if self.f.op(definition) != Op::SetVar || self.f.var_operand(definition, 0) != Some(var) {
            return Err(Fail);
        }
        let src = self.f.sub(definition, 1).ok_or(Fail)?;
        if self.f.op(src) != Op::AddressOf || self.f.var_operand(src, 0) != Some(target) {
            return Err(Fail);
        }
        self.add_chased(def, var);
        Ok(())
    }

    /// Bind a placeholder to whatever kind of hybrid node it faces.
    fn bind_any(&mut self, name: PhId, node: &Node) -> MResult<()> {
        if let Some(Binding::Member(m)) = self.binding(name) {
            let m = m.clone();
            return self.match_member_use(&m, node); // a read of the member's address
        }
        match node {
            Node::Rn(r) if r.op == HOp::Op(Op::AddressOf) && r.args.len() == 1 => match &r.args[0] {
                Node::Var(v, u) => {
                    let saved = self.use_index;
                    if *u >= 0 {
                        self.use_index = *u;
                    }
                    let result = self.bind_value(name, node, BindAction::Addr(*v));
                    self.use_index = saved;
                    result
                }
                _ => Err(Fail),
            },
            Node::Sited(e, u) => {
                let saved = self.use_index;
                self.use_index = *u as i32;
                let result = self.bind_any(name, &Node::Expr(*e));
                self.use_index = saved;
                result
            }
            Node::Expr(e) if self.f.op(*e) == Op::AddressOf && self.f.var_operand(*e, 0).is_some() => {
                let v = self.f.var_operand(*e, 0).unwrap();
                self.bind_value(name, node, BindAction::Addr(v))
            }
            Node::Var(v, u) => {
                let saved = self.use_index;
                if *u >= 0 {
                    self.use_index = *u;
                }
                let result = if matches!(self.binding(name), Some(Binding::Addr(_))) {
                    self.bind_addr_copy(name, *v)
                } else {
                    self.bind_value(name, node, BindAction::Var(*v))
                };
                self.use_index = saved;
                result
            }
            Node::Expr(e) => {
                let e = *e;
                if self.f.op(e) == Op::ConstPtr && self.binding(name).is_none() && self.check_types && self.typed(name) {
                    // The address of a global: the placeholder stands for that object
                    // when its type (or a member's starting there) suits the constraint.
                    let addr = self.f.const_value(e).unwrap_or(0) as u64;
                    let snap = self.snapshot();
                    match self.bind_global(name, addr, false) {
                        Ok(()) => return Ok(()),
                        Err(Fail) => self.restore(snap),
                    }
                }
                if let Some(existing) = self.binding(name) {
                    if self.f.op(e) == Op::Var {
                        let var = self.f.var_of(e);
                        if existing.bound_var(self.f).is_some() && existing.bound_var(self.f) == var {
                            return Ok(()); // a read of the very variable already bound (copies need not be followed)
                        }
                        if matches!(existing, Binding::Addr(_)) {
                            return self.bind_addr_copy(name, var.unwrap());
                        }
                    }
                }
                let saved = self.use_index;
                let result = self.bind_value(name, node, BindAction::ExprCopies(e));
                self.use_index = saved;
                result
            }
            Node::Const(c) => self.bind_int(name, *c),
            Node::Int(i) => self.bind_int(name, *i as i128),
            _ => Err(Fail), // a synthesized operation cannot become a call argument
        }
    }

    fn do_bind(&mut self, name: PhId, action: &BindAction) -> MResult<()> {
        match action {
            BindAction::Var(v) => self.bind_var(name, *v),
            BindAction::Addr(v) => self.bind_addr(name, *v),
            BindAction::ExprCopies(e) => {
                // A placeholder that already stands for a variable faces a copy of
                // it: follow the copies only as far as that variable, which may be
                // a link in the chain rather than its root (`$ret` is `x8_1`, the
                // code reads `temp0_2 = x8_1` where `x8_1 = temp0_1`).
                let stop = self.binding(name).and_then(|b| b.bound_var(self.f));
                let resolved = self.resolve_copies(*e, stop);
                self.bind_expr(name, resolved)
            }
        }
    }

    /// Bind a value use.  When a fresh binding fails and the value is the
    /// address of a member that satisfies the placeholder's type constraint,
    /// the placeholder stands for that member instead: a pointer to a struct is
    /// also the address of the member at its offset 0, and the field accesses
    /// that follow confirm or refute that reading.
    fn bind_value(&mut self, name: PhId, node: &Node, action: BindAction) -> MResult<()> {
        let typed = self.types.get(name.0 as usize).map(|t| t.is_some()).unwrap_or(false);
        if self.binding(name).is_some() || !self.check_types || !typed {
            return self.do_bind(name, &action);
        }
        let snap = self.snapshot();
        let use_index = self.use_index;
        match self.do_bind(name, &action) {
            Ok(()) => return Ok(()),
            Err(Fail) => {
                self.restore(snap);
                self.use_index = use_index;
            }
        }
        let (m, effective) = self.member_of(node, 0, true)?;
        if effective != m.offset {
            return Err(Fail);
        }
        self.check_type(name, Typed::Member(&m))?;
        self.set_binding(name, Binding::Member(m));
        Ok(())
    }

    fn bind_label(&mut self, label: LabelId, index: u32) -> MResult<()> {
        match self.labels[label.0 as usize] {
            None => {
                self.labels[label.0 as usize] = Some(index);
                Ok(())
            }
            Some(existing) if existing == index => Ok(()),
            _ => Err(Fail),
        }
    }

    // -- definition chasing -------------------------------------------------------
    /// Follow `v = w` copies so a placeholder binds to the original variable,
    /// stopping at `stop` when the chain reaches it.
    fn resolve_copies(&mut self, mut expr: ExprId, stop: Option<VarId>) -> ExprId {
        let mut seen = 0;
        while self.f.op(expr) == Op::Var && self.use_index >= 0 && seen < 8 {
            let Some(var) = self.f.var_of(expr) else { break };
            if Some(var) == stop {
                break;
            }
            let Some(def) = self.env.definition_of(self.f, self.use_index as u32, var) else { break };
            if self.is_extra_deleted(def) || self.is_blocked(def) {
                break;
            }
            let definition = self.f.instr(def);
            if self.f.op(definition) != Op::SetVar || self.f.var_operand(definition, 0) != Some(var) {
                break;
            }
            let Some(src) = self.f.sub(definition, 1) else { break };
            if self.f.op(src) != Op::Var {
                break;
            }
            self.add_chased(def, var);
            self.use_index = def as i32;
            expr = src;
            seen += 1;
        }
        expr
    }

    /// Match `pexpr` against the expression that defines `var` at the current use.
    fn chase(&mut self, pexpr: &Expr, var: VarId) -> MResult<()> {
        if self.use_index < 0 {
            return Err(Fail);
        }
        let def = self.env.definition_of(self.f, self.use_index as u32, var).ok_or(Fail)?;
        if (self.is_matched(def) && !self.is_absorbed(def)) || self.is_extra_deleted(def) || self.is_blocked(def) {
            self.refused_chase = true;
            return Err(Fail);
        }
        let definition = self.f.instr(def);
        let saved = self.use_index;
        self.use_index = def as i32;
        let result = if self.f.op(definition) == Op::SetVar && self.f.var_operand(definition, 0) == Some(var) {
            let src = self.f.sub(definition, 1).ok_or(Fail);
            src.and_then(|src| self.match_expr(pexpr, &Node::Expr(src)).map(|_| ()))
        } else if self.f.op(definition) == Op::Call && self.f.call_outputs(definition).as_slice() == [var] {
            match pexpr {
                Expr::Call(c) => self.match_call_expr(c, definition),
                _ => Err(Fail),
            }
        } else {
            Err(Fail)
        };
        self.use_index = saved;
        result?;
        self.add_chased(def, var);
        Ok(())
    }

    /// Match `call(target, args...)` against an `MLIL_CALL` instruction.
    fn match_call_expr(&mut self, pexpr: &CallExpr, instr: ExprId) -> MResult<()> {
        let dest = self.f.call_dest(instr).ok_or(Fail)?;
        match &pexpr.target {
            Expr::Symbol(s) => self.match_symbol(s, dest)?,
            other => {
                self.match_expr(other, &Node::Expr(dest))?;
            }
        }
        let params = self.f.call_params(instr);
        if pexpr.variadic {
            if params.len() < pexpr.args.len() {
                return Err(Fail);
            }
        } else if params.len() != pexpr.args.len() {
            return Err(Fail);
        }
        for (arg, param) in pexpr.args.iter().zip(params.iter()) {
            self.match_expr(arg, &Node::Expr(*param))?;
        }
        Ok(())
    }

    // -- expressions --------------------------------------------------------------
    /// Match a pattern expression against a hybrid node.  Returns the form the
    /// pattern was finally matched against: `node` itself, or the rewritten
    /// form when a rule was needed.  Facts about branch conditions are
    /// recorded in that form so that `when` conditions, which are built from
    /// the same code, compare equal to them.
    pub fn match_expr(&mut self, pexpr: &Expr, node: &Node) -> MResult<Node> {
        if let Node::Sited(e, u) = node {
            // A leaf carried over from another instruction: look things up from there.
            let saved = self.use_index;
            self.use_index = *u as i32;
            let result = self.match_expr(pexpr, &Node::Expr(*e));
            self.use_index = saved;
            result?;
            return Ok(node.clone());
        }
        match pexpr {
            Expr::Wildcard => return Ok(node.clone()),
            Expr::Placeholder(p) => {
                self.bind_any(*p, node)?;
                return Ok(node.clone());
            }
            _ => {}
        }
        let chaseable = matches!(pexpr, Expr::Op(_) | Expr::Const(_) | Expr::Symbol(_) | Expr::Call(_));
        if let Node::Var(v, u) = node {
            if !chaseable {
                return Err(Fail);
            }
            let saved = self.use_index;
            if *u >= 0 {
                self.use_index = *u;
            }
            let result = self.chase(pexpr, *v);
            self.use_index = saved;
            result?;
            return Ok(node.clone());
        }
        if let Node::Expr(e) = node {
            if self.f.op(*e) == Op::Var && chaseable && !matches!(pexpr, Expr::Op(o) if o.op == Op::Var) {
                // The pattern wants structure but the code has a variable: look at its definition.
                let var = self.f.var_of(*e).ok_or(Fail)?;
                self.chase(pexpr, var)?;
                return Ok(node.clone());
            }
        }
        match pexpr {
            Expr::Const(c) => {
                let value = node.const_value(self.f).ok_or(Fail)?;
                if !const_equal(value, *c, node.size(self.f).unwrap_or(0)) {
                    return Err(Fail);
                }
                Ok(node.clone())
            }
            Expr::Symbol(s) => {
                let e = node.expr_id().ok_or(Fail)?;
                self.match_symbol(s, e)?;
                Ok(node.clone())
            }
            Expr::Call(_) => Err(Fail), // a call result only appears through a variable (handled by chase)
            Expr::Op(o) => {
                if !node.is_code() && !node.is_rn() {
                    return Err(Fail);
                }
                let snap = self.snapshot();
                match self.match_op(o, node) {
                    Ok(()) => return Ok(node.clone()),
                    Err(Fail) => self.restore(snap),
                }
                if self.rule_depth >= MAX_RULE_DEPTH {
                    return Err(Fail);
                }
                let node_op = node.mlil_op(self.f);
                for (ri, rule) in self.rules.iter().enumerate() {
                    if rule.lhs_op() != node_op {
                        continue; // cannot apply: no snapshot, no attempt
                    }
                    let snap = self.snapshot();
                    let rewritten = match self.apply_rule(ri, rule, node) {
                        Ok(r) => r,
                        Err(Fail) => {
                            self.restore(snap);
                            continue;
                        }
                    };
                    self.rule_depth += 1;
                    let result = self.match_expr(pexpr, &rewritten);
                    self.rule_depth -= 1;
                    match result {
                        Ok(form) => return Ok(form),
                        Err(Fail) => self.restore(snap),
                    }
                }
                Err(Fail)
            }
            Expr::Wildcard | Expr::Placeholder(_) => unreachable!(),
        }
    }

    fn match_op(&mut self, pexpr: &crate::pattern::OpNode, node: &Node) -> MResult<()> {
        if node.mlil_op(self.f) != Some(pexpr.op) {
            return self.match_global_field(pexpr, node);
        }
        if let (Some(ps), Some(s)) = (pexpr.size, node.size(self.f)) {
            if s != ps {
                return Err(Fail);
            }
        }
        let operands = node.args(self.f);
        if operands.len() != pexpr.args.len() {
            return Err(Fail);
        }
        if pexpr.op.field_base_is_pointer().is_some() && pexpr.args.len() >= 2 {
            if let (Expr::Placeholder(p), Expr::Const(_)) = (&pexpr.args[0], &pexpr.args[1]) {
                // `load_struct.b($s, 0x17)` may face `load_struct.b(e, 0x2f)`: the string is
                // a member of what the code addresses.  The plain reading is tried first.
                if !matches!(self.binding(*p), Some(Binding::Member(_))) {
                    let snap = self.snapshot();
                    match self.match_operands(pexpr, &operands, 0) {
                        Ok(()) => return Ok(()),
                        Err(Fail) => self.restore(snap),
                    }
                }
                return self.match_member_field(pexpr, &operands);
            }
        }
        self.match_operands(pexpr, &operands, 0)
    }

    /// A field operation facing a plain load or store at a constant address:
    /// the object is a global (or a member of one) the code addresses
    /// directly, `[&g + 0x17].b` for `load_struct.b($s, 0x17)`.  The base
    /// placeholder stands for the object at the code's address less the
    /// pattern's offset (a pointer to it for `load_struct`/`store_struct`, the
    /// object itself for `var_field`/`set_var_field`).
    fn match_global_field(&mut self, pexpr: &crate::pattern::OpNode, node: &Node) -> MResult<()> {
        let (Some(flat), Some(pointer)) = (pexpr.op.flat_field_op(), pexpr.op.field_base_is_pointer()) else { return Err(Fail) };
        if node.mlil_op(self.f) != Some(flat) {
            return Err(Fail);
        }
        let (Some(Expr::Placeholder(name)), Some(Expr::Const(po))) = (pexpr.args.first(), pexpr.args.get(1)) else { return Err(Fail) };
        if let (Some(ps), Some(s)) = (pexpr.size, node.size(self.f)) {
            if s != ps {
                return Err(Fail);
            }
        }
        let operands = node.args(self.f);
        let stores = flat == Op::Store;
        if operands.len() != if stores { 2 } else { 1 } || pexpr.args.len() != if stores { 3 } else { 2 } {
            return Err(Fail);
        }
        let at = self.constant_address(&operands[0]).ok_or(Fail)?;
        let addr = (at as i128 - *po) as u64;
        self.bind_global(*name, addr, !pointer)?;
        if stores {
            self.match_operand(&pexpr.args[2], &operands[1])?;
        }
        Ok(())
    }

    /// An address the code spells as a constant: a constant pointer, or a sum
    /// of constants (`&g + 0x17`).
    fn constant_address(&self, node: &Node) -> Option<i64> {
        crate::hybrid::folded_const(self.f, &node.unsited()).map(|v| v as i64)
    }

    fn match_operands(&mut self, pexpr: &crate::pattern::OpNode, operands: &[Node], start: usize) -> MResult<()> {
        for (k, (arg, operand)) in pexpr.args.iter().zip(operands).enumerate() {
            if k < start {
                continue;
            }
            if pexpr.op.is_address_operand(k) {
                self.in_address += 1;
                let result = self.match_operand(arg, operand);
                self.in_address -= 1;
                result?;
            } else {
                self.match_operand(arg, operand)?;
            }
        }
        Ok(())
    }

    fn match_operand(&mut self, arg: &Expr, operand: &Node) -> MResult<()> {
        match operand {
            Node::Expr(_) | Node::Sited(_, _) | Node::Rn(_) => self.match_expr(arg, operand).map(|_| ()),
            Node::Var(v, u) => {
                let use_index = if *u >= 0 { *u } else { self.use_index };
                self.match_expr(arg, &Node::Var(*v, use_index)).map(|_| ())
            }
            Node::Int(_) | Node::Const(_) => {
                let value = operand.const_value(self.f).unwrap();
                match arg {
                    Expr::Wildcard => Ok(()),
                    Expr::Const(c) => {
                        if *c == value {
                            Ok(())
                        } else {
                            Err(Fail)
                        }
                    }
                    Expr::Placeholder(p) => self.bind_int(*p, value),
                    _ => Err(Fail),
                }
            }
            Node::Wildcard => Ok(()),
            Node::List(_, _) | Node::Float(_) | Node::Other | Node::Symbol(_) => {
                if matches!(arg, Expr::Wildcard) {
                    Ok(())
                } else {
                    Err(Fail)
                }
            }
        }
    }

    // -- members of bigger objects ---------------------------------------------------
    /// What a pointer value denotes: variable `v`'s value plus `k`, the address of
    /// `v` plus `k`, or some expression plus `k`.  Copies, additions of
    /// constants and address-of definitions are followed (they go with the
    /// region unless read elsewhere).
    pub(crate) fn resolve_pointer(&mut self, node: &Node, use_index: Option<i32>) -> (Pointee, i64) {
        let node = node.unsited();
        let mut use_index = use_index.unwrap_or(self.use_index);
        let var = match &node {
            Node::Var(v, u) => {
                if *u >= 0 {
                    use_index = *u;
                }
                Some(*v)
            }
            Node::Expr(e) if self.f.op(*e) == Op::Var => self.f.var_of(*e),
            _ => None,
        };
        if let Some(var) = var {
            let def = if use_index >= 0 { self.env.definition_of(self.f, use_index as u32, var) } else { None };
            if let Some(d) = def {
                if !self.is_extra_deleted(d) && !self.is_blocked(d) && (!self.is_matched(d) || self.is_absorbed(d)) {
                    let definition = self.f.instr(d);
                    if self.f.op(definition) == Op::SetVar && self.f.var_operand(definition, 0) == Some(var) {
                        if let Some(src) = self.f.sub(definition, 1) {
                            let sop = self.f.op(src);
                            let follow = sop == Op::Var
                                || sop == Op::AddressOf
                                || sop == Op::AddressOfField
                                || (sop == Op::Add
                                    && self.f.sub(src, 1).and_then(|c| self.f.const_value(c)).is_some());
                            if follow {
                                let result = self.resolve_pointer(&Node::Expr(src), Some(d as i32));
                                self.add_chased(d, var);
                                return result;
                            }
                        }
                    }
                }
            }
            return (Pointee::Ptr(var), 0);
        }
        let op = node.mlil_op(self.f);
        let args = node.args(self.f);
        if op == Some(Op::Add) && args.len() == 2 {
            if let Some(c) = args[1].const_value(self.f) {
                let (p, k) = self.resolve_pointer(&args[0], Some(use_index));
                return (p, k + c as i64);
            }
        }
        if matches!(op, Some(Op::AddressOf) | Some(Op::AddressOfField)) && !args.is_empty() {
            if let Node::Var(v, _) = &args[0] {
                let offset = if op == Some(Op::AddressOfField) && args.len() > 1 {
                    args[1].const_value(self.f)
                } else {
                    Some(0)
                };
                if let Some(offset) = offset {
                    return (Pointee::Addr(*v), offset as i64);
                }
            }
        }
        (Pointee::Expr(node), 0)
    }

    fn type_of_node(&self, node: &Node) -> Option<TypeId> {
        match node {
            Node::Expr(e) | Node::Sited(e, _) => self.env.type_of_expr(self.f, *e),
            Node::Var(v, _) => self.env.type_of_var(self.f, *v),
            _ => None,
        }
    }

    /// The member holding byte `offset` of the object `base` addresses (a
    /// pointer when `pointer`, else the variable holding the object), and
    /// that offset relative to the object the member belongs to.
    pub(crate) fn member_of(&mut self, base: &Node, offset: i64, pointer: bool) -> MResult<(MemberRef, i64)> {
        let (pointee, k, found) = if !pointer {
            let v = match base.unsited() {
                Node::Var(v, _) => v,
                _ => return Err(Fail),
            };
            let t = self.env.type_of_var(self.f, v);
            (Pointee::Addr(v), 0, t.and_then(|t| self.env.member_containing(t, offset, false)))
        } else {
            let (p, k) = self.resolve_pointer(base, None);
            let found = match &p {
                Pointee::Ptr(v) => self.env.type_of_var(self.f, *v).and_then(|t| self.env.member_containing(t, offset + k, true)),
                Pointee::Addr(v) => self.env.type_of_var(self.f, *v).and_then(|t| self.env.member_containing(t, offset + k, false)),
                Pointee::Expr(n) => self.type_of_node(n).and_then(|t| self.env.member_containing(t, offset + k, true)),
            };
            (p, k, found)
        };
        let (member_offset, ty) = found.ok_or(Fail)?;
        let kind = if !pointer { MemberKind::Var } else { pointee.kind() };
        let base = pointee.base().ok_or(Fail)?;
        Ok((MemberRef::new(kind, base, member_offset, Some(ty)), offset + k))
    }

    /// A field operation whose base placeholder stands for a string that is a
    /// member of the object the code addresses: the code's offset is the
    /// member's plus the pattern's, and the member's type must satisfy the
    /// placeholder's constraint.
    fn match_member_field(&mut self, pexpr: &crate::pattern::OpNode, operands: &[Node]) -> MResult<()> {
        if !self.check_types {
            return Err(Fail); // rules have no typed placeholders: nothing to normalise for them
        }
        let Expr::Placeholder(name) = pexpr.args[0] else { return Err(Fail) };
        let Expr::Const(po) = pexpr.args[1] else { return Err(Fail) };
        let pointer = pexpr.op.field_base_is_pointer().ok_or(Fail)?;
        let code_off = operands[1].const_value(self.f).ok_or(Fail)? as i64;
        match self.binding(name).cloned() {
            Some(Binding::Member(m)) => {
                let (kind, base, k) = if pointer {
                    let (p, k) = self.resolve_pointer(&operands[0], None);
                    (p.kind(), p.base(), k)
                } else {
                    match operands[0].unsited() {
                        Node::Var(v, _) => (MemberKind::Var, Some(MemberBase::Var(v)), 0),
                        _ => return Err(Fail),
                    }
                };
                let Some(base) = base else { return Err(Fail) };
                if !m.same_base(kind, base, self.f) || k + code_off != m.offset + po as i64 {
                    return Err(Fail);
                }
                // the code's offset must still fall inside that member: three zero
                // words at 0, 8 and 0x10 of a vector are its three pointers, not
                // a string living in the first one
                if self.member_of(&operands[0], code_off, pointer)?.0.offset != m.offset {
                    return Err(Fail);
                }
            }
            existing => {
                let (m, effective) = self.member_of(&operands[0], code_off, pointer)?;
                if effective - m.offset != po as i64 {
                    return Err(Fail);
                }
                match existing {
                    None => {
                        self.check_type(name, Typed::Member(&m))?;
                        self.set_binding(name, Binding::Member(m));
                    }
                    // bound to a plain variable or expression earlier: it must hold the member's address
                    Some(Binding::Expr { expr, .. }) => self.match_member_use(&m, &Node::Expr(expr))?,
                    Some(Binding::Var(v)) => {
                        let site = self.bind_site[name.0 as usize];
                        self.match_member_use(&m, &Node::Var(v, site))?;
                    }
                    Some(_) => return Err(Fail),
                }
            }
        }
        self.match_operands(pexpr, operands, 2)
    }

    /// A value the code passes where the pattern names the member: it must be
    /// the member's address (base + offset, the field's address, or the
    /// object's own pointer for a member at offset 0).
    fn match_member_use(&mut self, m: &MemberRef, node: &Node) -> MResult<()> {
        let (p, k) = self.resolve_pointer(node, None);
        if k != m.offset {
            return Err(Fail);
        }
        if let Some(base) = p.base() {
            if m.same_base(p.kind(), base, self.f) {
                return Ok(());
            }
        }
        if m.kind == MemberKind::Var {
            if let Pointee::Addr(v) = p {
                if m.base == MemberBase::Var(v) {
                    return Ok(()); // the address of the member held in a variable
                }
            }
        }
        Err(Fail)
    }

    fn match_symbol(&mut self, sym: &SymbolRef, e: ExprId) -> MResult<()> {
        if !self.f.op(e).is_symbol_op() {
            return Err(Fail);
        }
        let addr = self.f.int_operand(e, 0).ok_or(Fail)? as u64;
        let names = self.env.symbol_names_at(addr);
        let found = if sym.is_glob() {
            // A quoted name with wildcards matches any of the address's names, so a
            // library routine can be named without its full mangled or templated form.
            names.iter().any(|n| glob_match(&sym.name, n))
        } else {
            names.contains(&sym.name)
        };
        if !found {
            let (want, have) = (sym.name.clone(), names.first().cloned().unwrap_or_else(|| format!("{addr:#x}")));
            return Err(self.why(|| format!("the target is {have}, not {want}")));
        }
        Ok(())
    }

    // -- rewrite rules -------------------------------------------------------------
    /// Match the rule's left side against `node` and return its instantiated
    /// right side.
    ///
    /// For an unconditional rule on a code expression the outcome depends only
    /// on the expression, the instruction it is read from and which
    /// definitions may be followed, so it is memoized per round: the rewritten
    /// form is kept with the definitions it followed and reused wherever
    /// following them is still allowed, and a failure that refused no chase is
    /// final.  Every pattern tries every rule at every mismatch, so the same
    /// expression is rewritten many times per round otherwise.
    fn apply_rule(&mut self, ri: usize, rule: &'a Rule, node: &Node) -> MResult<Node> {
        let key = if rule.when.is_none() { Some((ri, self.use_index, node.clone())) } else { None };
        if let Some(key) = &key {
            let entry = self.round.memo.borrow().get(key).cloned();
            if let Some(entry) = entry {
                let Some((rewritten, chased)) = entry else { return Err(Fail) };
                for (d, _) in &chased {
                    if self.is_extra_deleted(*d) || self.is_blocked(*d) {
                        return Err(Fail); // a fresh attempt would refuse the same chase
                    }
                }
                for (d, v) in chased {
                    self.add_chased(d, v);
                }
                return Ok(rewritten);
            }
        }
        let mut sub = self.for_rule(rule);
        if sub.match_expr(&rule.lhs, node).is_err() {
            if let Some(key) = key {
                if !sub.refused_chase {
                    self.round.memo.borrow_mut().insert(key, None);
                }
            }
            return Err(Fail);
        }
        if let Some(when) = &rule.when {
            let cond = instantiate(when, &sub.bindings, &sub.bind_site)?;
            if !self.fact_holds(&cond) {
                return Err(Fail);
            }
        }
        for (d, v) in &sub.chased {
            self.add_chased(*d, *v);
        }
        let rewritten = instantiate(&rule.rhs, &sub.bindings, &sub.bind_site)?;
        if let Some(key) = key {
            self.round.memo.borrow_mut().insert(key, Some((rewritten.clone(), sub.chased.clone())));
        }
        Ok(rewritten)
    }

    /// Follow `v = w` copies back from `use_index` to the original variable.
    fn root_var(&self, mut var: VarId, mut use_index: i32) -> VarId {
        let mut seen = 0;
        while use_index >= 0 && seen < 8 {
            let Some(def) = self.env.definition_of(self.f, use_index as u32, var) else { break };
            let definition = self.f.instr(def);
            if self.f.op(definition) != Op::SetVar || self.f.var_operand(definition, 0) != Some(var) {
                break;
            }
            let Some(src) = self.f.sub(definition, 1) else { break };
            let Some(v) = self.f.var_of(src) else { break };
            var = v;
            use_index = def as i32;
            seen += 1;
        }
        var
    }

    /// Two variable reads denote the same value when they resolve to the same
    /// variable through plain copies.
    fn vars_equivalent(&self, va: VarId, ia: i32, vb: VarId, ib: i32) -> bool {
        va == vb || self.root_var(va, ia) == self.root_var(vb, ib)
    }

    pub fn fact_holds(&self, cond: &Node) -> bool {
        let (key, polarity) = normalize_condition(self.f, cond, true);
        let eq = |va: VarId, ia: i32, vb: VarId, ib: i32| self.vars_equivalent(va, ia, vb, ib);
        self.facts
            .iter()
            .any(|(fact, fp)| *fp == polarity && hybrid_equal(self.f, fact, &key, Some(&eq), -1, -1))
    }

    fn add_fact(&self, facts: &[Fact], cond: &Node, polarity: bool) -> Vec<Fact> {
        let (key, pol) = normalize_condition(self.f, cond, polarity);
        let mut out = facts.to_vec();
        out.push((key, pol));
        out
    }

    /// Facts for a block where the pattern guard is `polarity`: the guard as
    /// the pattern spells it and as the code spelled it (`form`, which has the
    /// guard's polarity when `direct`), so that `when` conditions built from
    /// either spelling are found.
    pub fn guard_facts(&self, facts: &[Fact], guard: &Node, form: &Node, direct: bool, polarity: bool) -> Vec<Fact> {
        let out = self.add_fact(facts, guard, polarity);
        if form.is_code() || form.is_rn() {
            return self.add_fact(&out, form, if direct { polarity } else { !polarity });
        }
        out
    }

    /// Match a pattern's branch condition against the code's: as written,
    /// negated, or against the code's complement (rewrite rules are written
    /// for the spellings the compiler emits, which may be the complement of
    /// the pattern's test).  Returns the form the pattern was matched against,
    /// whether the branch targets are swapped, and whether that form has the
    /// polarity of `pcond` rather than of its negation.
    fn match_condition(&mut self, pcond: &Expr, cond: &Node) -> MResult<(Node, bool, bool)> {
        let negated = negate(pcond);
        let complement = complement_of(self.f, cond);
        let mut attempts: Vec<(&Expr, &Node, bool, bool)> = vec![(pcond, cond, false, true)];
        if let Some(n) = &negated {
            attempts.push((n, cond, true, false));
        }
        if let Some(c) = &complement {
            attempts.push((pcond, c, true, true));
            if let Some(n) = &negated {
                attempts.push((n, c, false, false));
            }
        }
        for (pexpr, node, swapped, direct) in attempts {
            let snap = self.snapshot();
            match self.match_expr(pexpr, node) {
                Ok(form) => return Ok((form, swapped, direct)),
                Err(Fail) => self.restore(snap),
            }
        }
        Err(Fail)
    }

    // -- statements --------------------------------------------------------------
    pub fn match_stmt(&mut self, stmt: &Stmt, instr: ExprId) -> MResult<()> {
        let op = self.f.op(instr);
        match stmt {
            Stmt::SetVar { dest, src } => {
                if op != Op::SetVar {
                    return Err(self.why(|| format!("expects an assignment, the code has {}", op.name())));
                }
                let dest_var = self.f.var_operand(instr, 0).ok_or(Fail)?;
                let src_e = self.f.sub(instr, 1).ok_or(Fail)?;
                if let Dest::Ph(p) = dest {
                    self.bind_var(*p, dest_var)?;
                    if *p == RET {
                        self.ret_size = self.f.size(instr);
                    }
                }
                self.match_expr(src, &Node::Expr(src_e))?;
                Ok(())
            }
            Stmt::Store { size, dest, src } => {
                if op != Op::Store {
                    return Err(self.why(|| format!("expects a store, the code has {}", op.name())));
                }
                if let Some(s) = size {
                    if self.f.size(instr) != *s {
                        return Err(self.why(|| format!("the store is {} bytes wide, not {s}", self.f.size(instr))));
                    }
                }
                let d = self.f.sub(instr, 0).ok_or(Fail)?;
                let s = self.f.sub(instr, 1).ok_or(Fail)?;
                self.in_address += 1;
                let r = self.match_expr(dest, &Node::Expr(d));
                self.in_address -= 1;
                r?;
                self.match_expr(src, &Node::Expr(s))?;
                Ok(())
            }
            Stmt::Call(c) => {
                if op == Op::SetVar && c.outputs.len() == 1 && !c.extra_outputs {
                    if let Dest::Ph(p) = c.outputs[0] {
                        let src = self.f.sub(instr, 1).ok_or(Fail)?;
                        if self.f.op(src) == Op::Var {
                            // `$x = call(f, ...)` facing `x = v` where v holds the result of such a
                            // call made earlier: the call is followed to its definition, which must
                            // be pure (it is evaluated again inside the outlined function) and goes
                            // with the region unless something else still reads its result.
                            let dest = self.f.var_operand(instr, 0).ok_or(Fail)?;
                            let var = self.f.var_of(src).ok_or(Fail)?;
                            if self.use_index < 0 {
                                return Err(Fail);
                            }
                            let def = self.env.definition_of(self.f, self.use_index as u32, var).ok_or(Fail)?;
                            if self.f.instr_op(def) != Op::Call || !self.env.is_pure_call(self.f, def) {
                                return Err(Fail);
                            }
                            self.bind_var(p, dest)?;
                            let call = Expr::Call(Box::new(CallExpr {
                                target: c.target.clone(),
                                args: c.args.clone(),
                                variadic: c.variadic,
                            }));
                            self.match_expr(&call, &Node::Expr(src))?;
                            return Ok(());
                        }
                    }
                }
                if op != Op::Call {
                    return Err(self.why(|| format!("expects a call, the code has {}", op.name())));
                }
                let outputs = self.f.call_outputs(instr);
                if outputs.len() < c.outputs.len() || (outputs.len() > c.outputs.len() && !c.extra_outputs) {
                    return Err(self.why(|| format!("the call has {} output(s), the pattern names {}", outputs.len(), c.outputs.len())));
                }
                for (wanted, out) in c.outputs.iter().zip(outputs.iter()) {
                    if let Dest::Ph(p) = wanted {
                        self.bind_var(*p, *out)?;
                    }
                }
                if c.extra_outputs {
                    self.clobbered.extend_from_slice(&outputs[c.outputs.len()..]);
                }
                let dest = self.f.call_dest(instr).ok_or(Fail)?;
                match &c.target {
                    Expr::Symbol(s) => self.match_symbol(s, dest)?,
                    other => {
                        self.match_expr(other, &Node::Expr(dest))?;
                    }
                }
                let params = self.f.call_params(instr);
                if c.variadic {
                    if params.len() < c.args.len() {
                        return Err(self.why(|| format!("the call passes {} argument(s), the pattern needs at least {}", params.len(), c.args.len())));
                    }
                } else if params.len() != c.args.len() {
                    return Err(self.why(|| format!("the call passes {} argument(s), the pattern {}", params.len(), c.args.len())));
                }
                for (arg, param) in c.args.iter().zip(params.iter()) {
                    self.match_expr(arg, &Node::Expr(*param))?;
                }
                Ok(())
            }
            Stmt::Intrinsic(c) => {
                if op != Op::Intrinsic {
                    return Err(self.why(|| format!("expects an intrinsic, the code has {}", op.name())));
                }
                let outputs = self.f.vars_written(instr);
                if outputs.len() < c.outputs.len() || (outputs.len() > c.outputs.len() && !c.extra_outputs) {
                    return Err(self.why(|| format!("the intrinsic has {} output(s), the pattern names {}", outputs.len(), c.outputs.len())));
                }
                for (wanted, out) in c.outputs.iter().zip(outputs.iter()) {
                    if let Dest::Ph(p) = wanted {
                        self.bind_var(*p, *out)?;
                    }
                }
                if c.extra_outputs {
                    self.clobbered.extend_from_slice(&outputs[c.outputs.len()..]);
                }
                let Operand::Intrinsic(index) = self.f.operand(instr, 1) else { return Err(Fail) };
                let name = self.f.intrinsic_name(index).ok_or(Fail)?;
                let named = if c.name.is_glob() { glob_match(&c.name.name, name) } else { c.name.name == name };
                if !named {
                    let (have, want) = (name.to_string(), c.name.name.clone());
                    return Err(self.why(|| format!("the intrinsic is {have}, not {want}")));
                }
                let params: Vec<ExprId> = self
                    .f
                    .list(self.f.operand(instr, 2))
                    .iter()
                    .filter_map(|o| if let Operand::Expr(e) = o { Some(*e) } else { None })
                    .collect();
                if c.variadic {
                    if params.len() < c.args.len() {
                        return Err(Fail);
                    }
                } else if params.len() != c.args.len() {
                    return Err(Fail);
                }
                for (arg, param) in c.args.iter().zip(params.iter()) {
                    self.match_expr(arg, &Node::Expr(*param))?;
                }
                Ok(())
            }
            Stmt::Ret(values) => {
                if op == Op::Tailcall && values.len() == 1 {
                    if let Expr::Call(c) = &values[0] {
                        return self.match_call_expr(c, instr); // `return call(...)`: a tail call
                    }
                }
                if op != Op::Ret {
                    return Err(self.why(|| format!("expects a return, the code has {}", op.name())));
                }
                let list = self.f.operands(instr).first().copied().ok_or(Fail)?;
                let items: Vec<Node> = self.f.list(list).iter().map(|o| Node::from_operand(*o)).collect();
                if items.len() != values.len() {
                    return Err(Fail);
                }
                for (arg, value) in values.iter().zip(items.iter()) {
                    self.match_operand(arg, value)?;
                }
                Ok(())
            }
            Stmt::Nop => {
                if op != Op::Nop {
                    return Err(self.why(|| format!("expects nop, the code has {}", op.name())));
                }
                Ok(())
            }
            Stmt::Expr(e) => self.match_expr(e, &Node::Expr(instr)).map(|_| ()),
            Stmt::If { .. } | Stmt::Goto(_) => Err(Fail),
        }
    }

    /// Match one statement at `index`; roll back all bindings on failure.
    fn try_stmt(&mut self, stmt: &Stmt, index: u32) -> bool {
        let snap = self.snapshot();
        self.attempt(index);
        self.use_index = index as i32;
        let result = self.match_stmt(stmt, self.f.instr(index));
        self.use_index = -1;
        match result {
            Ok(()) => {
                self.set_matched(index);
                self.advance();
                true
            }
            Err(Fail) => {
                self.settle();
                self.restore(snap);
                false
            }
        }
    }

    // -- explaining --------------------------------------------------------------
    /// Records that the current pattern statement is being tried at `index`.
    fn attempt(&mut self, index: u32) {
        if let Some(t) = &mut self.trace {
            t.current = Attempt { matched: t.matched, block: self.current_block, stmt: self.current_stmt, instr: index, reason: None };
        }
    }

    /// The current statement matched.
    fn advance(&mut self) {
        if let Some(t) = &mut self.trace {
            t.matched += 1;
        }
    }

    /// The current attempt failed: keep it when it got further than any before
    /// (the first attempt at a depth is the telling one).
    fn settle(&mut self) {
        if let Some(t) = &mut self.trace {
            if t.current.matched > t.best.matched || t.best.reason.is_none() {
                t.best = t.current.clone();
            }
        }
    }

    /// Why the current attempt is failing, when explaining (the first reason
    /// of an attempt is the one kept).
    fn why(&mut self, reason: impl FnOnce() -> String) -> Fail {
        if let Some(t) = &mut self.trace {
            if t.current.reason.is_none() {
                t.current.reason = Some(reason());
            }
        }
        Fail
    }

    // -- blocks ------------------------------------------------------------------
    fn facts_slot(label: Option<LabelId>) -> usize {
        label.map(|l| l.0 as usize + 1).unwrap_or(0)
    }

    fn match_block(&mut self, pblock: &PBlock, index: u32, is_entry: bool, is_last: bool) -> MResult<()> {
        if index as usize >= self.f.len() {
            return Err(Fail);
        }
        let block = self.f.block_of(index);
        let (bstart, bend, bid) = (block.start, block.end, block.id);
        if !is_entry && index != bstart {
            return Err(Fail);
        }
        if let Some(label) = pblock.label {
            // A branch back to this block must land where it was matched.
            self.bind_label(label, index)?;
        }
        self.facts = self.block_facts[Self::facts_slot(pblock.label)].clone();
        self.absorbable = !is_entry; // the entry block keeps interleaved code in place instead
        let mut cur = index;
        for (n, stmt) in pblock.stmts.iter().enumerate() {
            // Interleaved instructions are only tolerated between matched
            // statements of the entry block, never before the first one.
            let allow_kept = is_entry && n > 0;
            self.current_stmt = n;
            cur = match stmt {
                Stmt::Goto(label) => self.match_goto(*label, bid, cur, allow_kept)?,
                Stmt::If { cond, t, f } => self.match_if(cond, *t, *f, bid, cur, allow_kept)?,
                _ => self.match_plain(stmt, bid, cur, allow_kept)?,
            };
        }
        if is_entry {
            let mut first = None;
            let mut last = None;
            for i in bstart..bend {
                if self.is_matched(i) {
                    first.get_or_insert(i);
                    last = Some(i);
                }
            }
            let (Some(first), Some(last)) = (first, last) else { return Err(Fail) };
            self.entry_first = Some(first);
            self.entry_last = Some(last);
        }
        if !is_last {
            if cur != bend {
                return Err(Fail);
            }
            if !is_entry {
                self.internal_blocks.push(bid);
            }
        } else if is_entry {
            self.exit_index = Some(cur);
            self.exit_goto = false;
        } else {
            self.exit_index = Some(bstart);
            self.exit_goto = true;
        }
        Ok(())
    }

    /// An unmatched pure assignment inside an arm block goes with the region:
    /// the compiler interleaves copies of values computed elsewhere with the
    /// arm's own statements (`x1_2 = __s` before a call that passes it), and
    /// a pattern need not spell them.  The post-checks make sure nothing
    /// outside the region reads what such an instruction wrote.
    fn absorb(&mut self, index: u32) -> bool {
        let op = self.f.instr_op(index);
        if !self.absorbable || op != Op::SetVar || op.is_impure() {
            return false;
        }
        if !self.absorbed_set.contains(index as usize) {
            self.absorbed_set.insert(index as usize);
            self.absorbed.push(index);
        }
        true
    }

    fn match_plain(&mut self, stmt: &Stmt, block: BlockId, mut cur: u32, allow_kept: bool) -> MResult<u32> {
        let image = image_store(stmt).map_err(|_| Fail)?;
        let last = self.f.block(block).end;
        while cur < last {
            if self.is_extra_deleted(cur) {
                cur += 1;
                continue;
            }
            if let Some(image) = &image {
                if let Some(end) = self.try_image(image, cur, last) {
                    return Ok(end);
                }
            } else if self.try_stmt(stmt, cur) {
                return Ok(cur + 1);
            }
            if !allow_kept && !self.absorb(cur) {
                return Err(Fail);
            }
            cur += 1;
        }
        self.attempt(last);
        self.why(|| "the block ends before this statement".to_string());
        self.settle();
        Err(Fail)
    }

    // -- byte images ------------------------------------------------------------
    /// Match a run of constant stores beginning at `start`; the index after
    /// the run, or None with every binding rolled back.
    fn try_image(&mut self, image: &ImageStore, start: u32, end: u32) -> Option<u32> {
        let snap = self.snapshot();
        match self.match_image(image, start, end) {
            Ok(end) => Some(end),
            Err(Fail) => {
                self.restore(snap);
                None
            }
        }
    }

    /// `set_var_field($v, off, const_data($chars, $n))`: consecutive stores of
    /// constants into one variable (or into one global, through constant
    /// addresses) that together spell `$n` characters and a terminator from
    /// offset `off`, in whatever widths and order the compiler chose
    /// (overlapping stores must agree).  The run ends with the store that
    /// completes the text; `$chars` receives the characters packed little-endian
    /// and `$n` their count.  Text longer than a register can hold must be the
    /// binary's own copy of the literal (the stores load from it), so that the
    /// outlined call can point at it.
    fn match_image(&mut self, image: &ImageStore, start: u32, end: u32) -> MResult<u32> {
        let base = match image.offset {
            IntArg::Const(c) => c as i64,
            IntArg::Ph(p) => self.resolve_int(p, false)?.ok_or(Fail)? as i64,
        };
        let wanted: Option<i64> = match image.length {
            LenArg::Wildcard => None,
            LenArg::Const(c) => Some(c as i64),
            LenArg::Ph(p) => self.resolve_int(p, true)?.map(|v| v as i64),
        };
        if wanted.map(|w| w < 0).unwrap_or(false) {
            return Err(Fail);
        }
        let mut var: Option<VarId> = None;
        let mut global: Option<(u64, u64)> = None; // the object's address and the start of the global holding it
        let mut shift: i64 = 0; // where the member starts inside the variable, if the text goes into one
        let mut pieces: BTreeMap<i64, u8> = BTreeMap::new(); // offset within the object -> byte
        let mut consumed: Vec<(u32, i64, usize)> = Vec::new(); // (instruction, offset, size) of each store taken
        let mut origin: Option<u64> = None; // where the binary holds the byte at `base`
        let mut text: Option<Vec<u8>> = None;
        let mut cur = start;
        while cur < end {
            let instr = self.f.instr(cur);
            let op = self.f.op(instr);
            if (var.is_some() || global.is_some())
                && matches!(op, Op::SetVar | Op::SetVarField)
                && (global.is_some() || self.f.var_operand(instr, 0) != var)
                && !op.is_impure()
            {
                // an assignment to something else in the middle of the run: the
                // vector-register hop of a wide load, or an unrelated value that
                // stays in place
                cur += 1;
                continue;
            }
            let (offset, src) = match op {
                Op::SetVarField if global.is_none() => {
                    let dest = self.f.var_operand(instr, 0).ok_or(Fail)?;
                    let Some(offset) = self.f.int_operand(instr, 1) else { break };
                    if var.map(|v| dest != v).unwrap_or(false) {
                        break;
                    }
                    if var.is_none() {
                        self.use_index = cur as i32;
                        let bound = self.bind_field_base(image.dest, dest, offset);
                        self.use_index = -1;
                        shift = bound?;
                        var = Some(dest);
                    }
                    (offset - shift, self.f.sub(instr, 2).ok_or(Fail)?)
                }
                Op::Store if var.is_none() => {
                    // a global the code addresses directly
                    let Some(at) = self.f.sub(instr, 0).and_then(|a| self.constant_address(&Node::Expr(a))) else { break };
                    let at = at as u64;
                    if global.is_none() {
                        self.use_index = cur as i32;
                        let bound = self.bind_image_global(image.dest, at);
                        self.use_index = -1;
                        global = Some(bound?);
                    }
                    let (object, holder) = global.unwrap();
                    // the same global, from the object on
                    if at < object || self.env.data_var_containing(at).map(|(s, _)| s) != Some(holder) {
                        break;
                    }
                    ((at - object) as i64, self.f.sub(instr, 1).ok_or(Fail)?)
                }
                _ => break,
            };
            self.use_index = cur as i32;
            let data = self.constant_bytes(src, self.f.size(instr) as usize);
            self.use_index = -1;
            let Some((raw, address)) = data else { break };
            for (i, b) in raw.iter().enumerate() {
                match pieces.get(&(offset + i as i64)) {
                    Some(existing) if existing != b => return Err(Fail),
                    Some(_) => {}
                    None => {
                        pieces.insert(offset + i as i64, *b);
                    }
                }
            }
            if let Some(address) = address {
                if origin.is_none() {
                    origin = Some((address as i64 - (offset - base)) as u64);
                }
            }
            consumed.push((cur, offset, raw.len()));
            self.set_matched(cur);
            cur += 1;
            text = image_text(&pieces, base, wanted, true)?;
            if text.is_some() {
                break;
            }
        }
        if text.is_none() {
            // The run ended without a terminator: the object was zeroed beforehand
            // (a memset the compiler relied on).  The text is what was stored,
            // provided it is contiguous and no longer than a bound count says;
            // trailing stores outside it (the size byte) are given back.
            text = image_text(&pieces, base, wanted, false)?;
            if let Some(t) = &text {
                if !t.is_empty() {
                    let inside: Vec<bool> =
                        consumed.iter().map(|(_, off, n)| *off + *n as i64 <= base + t.len() as i64 && *off >= base).collect();
                    let mut keep = inside.len();
                    while keep > 0 && !inside[keep - 1] {
                        keep -= 1;
                    }
                    if !inside[..keep].iter().all(|x| *x) {
                        return Err(Fail);
                    }
                    for (index, _, _) in &consumed[keep..] {
                        self.unmatch(*index);
                    }
                    if keep < consumed.len() {
                        cur = consumed[keep].0;
                    }
                }
            }
        }
        let text = match text {
            Some(t) if !t.is_empty() => t,
            _ => return Err(Fail),
        };
        if let Some(o) = origin {
            let mut expected = text.clone();
            expected.push(0);
            if self.env.read_bytes(o, text.len() + 1).as_deref() != Some(expected.as_slice()) {
                origin = None;
            }
        }
        if text.len() > 8 && origin.is_none() {
            // Longer text cannot ride in a register: it must be the binary's own
            // copy (the decompiler folds short loads from it into immediates).
            let mut terminated = text.clone();
            terminated.push(0);
            origin = Some(self.env.find_bytes(&terminated).ok_or(Fail)?);
        }
        self.use_index = cur as i32 - 1;
        let result = (|| -> MResult<()> {
            if let LenArg::Ph(p) = image.length {
                self.bind_known_int(p, text.len() as i128)?;
            }
            if let Some(p) = image.chars {
                self.bind_known_bytes(p, &text, origin)?;
            }
            Ok(())
        })();
        self.use_index = -1;
        result?;
        Ok(cur)
    }

    /// Bind a placeholder to an integer the matcher computed, or check it
    /// against the constant the placeholder already stands for.
    fn bind_known_int(&mut self, name: PhId, value: i128) -> MResult<()> {
        if self.binding(name).is_some() {
            if self.resolve_int(name, false)? != Some(value) {
                return Err(Fail);
            }
            return Ok(());
        }
        self.set_binding(name, Binding::Int { value, origin: None });
        Ok(())
    }

    fn bind_known_bytes(&mut self, name: PhId, bytes: &[u8], origin: Option<u64>) -> MResult<()> {
        if self.binding(name).is_some() {
            let packed = crate::binding::bytes_to_i128(bytes);
            if packed.is_none() || self.resolve_int(name, false)? != packed {
                return Err(Fail);
            }
            return Ok(());
        }
        self.set_binding(name, Binding::Bytes { bytes: bytes.into(), origin });
        Ok(())
    }

    /// Bind the placeholder a run of field stores writes: the variable itself
    /// when its type fits, else the member of it that holds `code_off`.
    /// Returns the offset the member starts at (0 for the variable itself).
    fn bind_field_base(&mut self, name: PhId, var: VarId, code_off: i64) -> MResult<i64> {
        let existing = self.binding(name).cloned();
        if let Some(Binding::Member(m)) = &existing {
            if m.kind != MemberKind::Var
                || m.base != MemberBase::Var(var)
                || self.member_of(&Node::Var(var, -1), code_off, false)?.0.offset != m.offset
            {
                return Err(Fail);
            }
            return Ok(m.offset);
        }
        let snap = self.snapshot();
        match self.bind_var(name, var) {
            Ok(()) => return Ok(0),
            Err(Fail) => self.restore(snap),
        }
        if existing.is_some() {
            return Err(Fail);
        }
        let (m, _) = self.member_of(&Node::Var(var, -1), code_off, false)?;
        self.check_type(name, Typed::Member(&m))?;
        let offset = m.offset;
        self.set_binding(name, Binding::Member(m));
        Ok(offset)
    }

    /// Bind the placeholder a run of stores to constant addresses writes: the
    /// global object it already stands for, else the outermost object around
    /// `at` (the global, or a member of it) whose type suits the placeholder.
    /// Returns the object's address and the start of the global holding it.
    fn bind_image_global(&mut self, name: PhId, at: u64) -> MResult<(u64, u64)> {
        let holder = self.env.data_var_containing(at).ok_or(Fail)?.0;
        if let Some(existing) = self.binding(name) {
            return match existing {
                Binding::Global { addr, object: true } if *addr <= at => Ok((*addr, holder)),
                _ => Err(Fail),
            };
        }
        for object in self.global_objects_around(at) {
            let snap = self.snapshot();
            match self.bind_global(name, object, true) {
                Ok(()) => return Ok((object, holder)),
                Err(Fail) => self.restore(snap),
            }
        }
        Err(Fail)
    }

    /// The integer an int-bound placeholder stands for; None when unbound and `missing_ok`.
    fn resolve_int(&self, name: PhId, missing_ok: bool) -> MResult<Option<i128>> {
        match self.binding(name) {
            None => {
                if missing_ok {
                    Ok(None)
                } else {
                    Err(Fail)
                }
            }
            Some(b @ (Binding::Int { .. } | Binding::Bytes { .. } | Binding::Expr { .. })) => {
                b.const_value(self.f).map(Some).ok_or(Fail)
            }
            Some(_) => Err(Fail),
        }
    }

    /// The `size` bytes a store's value is known to hold, and the address the
    /// binary holds them at when the code loaded them from there: an
    /// immediate, a load from a constant address, or a variable defined as one
    /// of those (its definition then goes with the region).
    fn constant_bytes(&mut self, node: ExprId, size: usize) -> Option<(Vec<u8>, Option<u64>)> {
        if let Some(value) = self.f.const_value(node) {
            let bytes = (value as u128).to_le_bytes();
            return Some((bytes[..size.min(16)].to_vec(), None));
        }
        match self.f.op(node) {
            Op::Load => {
                let addr = self.f.sub(node, 0).and_then(|a| self.f.const_value(a))? as u64;
                let raw = self.env.read_bytes(addr, size)?;
                Some((raw, Some(addr)))
            }
            op @ (Op::Var | Op::VarField) if self.use_index >= 0 => {
                // A variable (or a field of one, as a 16-byte load lands in a vector
                // register) defined as one of those forms.
                let var = self.f.var_operand(node, 0)?;
                let def = self.env.definition_of(self.f, self.use_index as u32, var)?;
                if (self.is_matched(def) && !self.is_absorbed(def)) || self.is_extra_deleted(def) || self.is_blocked(def) {
                    return None;
                }
                let definition = self.f.instr(def);
                let src = if op == Op::Var {
                    if self.f.op(definition) != Op::SetVar || self.f.var_operand(definition, 0) != Some(var) {
                        return None;
                    }
                    self.f.sub(definition, 1)?
                } else {
                    if self.f.op(definition) != Op::SetVarField
                        || self.f.var_operand(definition, 0) != Some(var)
                        || self.f.int_operand(definition, 1) != self.f.int_operand(node, 1)
                        || (Some(self.f.size(definition)).filter(|s| *s != 0).unwrap_or(size as u16) as usize) != size
                    {
                        return None;
                    }
                    self.f.sub(definition, 2)?
                };
                let saved = self.use_index;
                self.use_index = def as i32;
                let result = self.constant_bytes(src, size);
                self.use_index = saved;
                if result.is_some() {
                    self.add_chased(def, var);
                }
                result
            }
            _ => None,
        }
    }

    fn match_if(&mut self, cond: &Expr, t: LabelId, f: LabelId, block: BlockId, mut cur: u32, allow_kept: bool) -> MResult<u32> {
        let end = self.f.block(block).end;
        while cur < end {
            let instr = self.f.instr(cur);
            if self.f.op(instr) == Op::If {
                let snap = self.snapshot();
                self.attempt(cur);
                self.use_index = cur as i32;
                let result = (|| -> MResult<u32> {
                    let code_cond = self.f.sub(instr, 0).ok_or(Fail)?;
                    let (tt, ft) = self.f.if_targets(instr).ok_or(Fail)?;
                    let (form, swapped, direct) = self.match_condition(cond, &Node::Expr(code_cond))?;
                    let (true_label, false_label) = if swapped { (f, t) } else { (t, f) };
                    self.bind_label(true_label, tt)?;
                    self.bind_label(false_label, ft)?;
                    // The pattern's guard holds in the block its true label names and
                    // fails in the other one.
                    let guard = instantiate(cond, &self.bindings, &self.bind_site)?;
                    let true_facts = self.guard_facts(&self.facts, &guard, &form, direct, true);
                    let false_facts = self.guard_facts(&self.facts, &guard, &form, direct, false);
                    self.block_facts[Self::facts_slot(Some(t))] = true_facts;
                    self.block_facts[Self::facts_slot(Some(f))] = false_facts;
                    self.set_matched(cur);
                    Ok(cur + 1)
                })();
                self.use_index = -1;
                return match result {
                    Ok(next) => {
                        self.advance();
                        Ok(next)
                    }
                    Err(Fail) => {
                        self.why(|| "the branch condition does not match".to_string());
                        self.settle();
                        self.restore(snap);
                        Err(Fail)
                    }
                };
            }
            if self.is_extra_deleted(cur) {
                cur += 1;
                continue;
            }
            if !allow_kept && !self.absorb(cur) {
                self.attempt(cur);
                self.why(|| format!("expects a branch, the code has {}", self.f.instr_op(cur).name()));
                self.settle();
                return Err(Fail);
            }
            cur += 1;
        }
        self.attempt(end);
        self.why(|| "the block ends before the pattern's branch".to_string());
        self.settle();
        Err(Fail)
    }

    fn match_goto(&mut self, label: LabelId, block: BlockId, mut cur: u32, allow_kept: bool) -> MResult<u32> {
        let end = self.f.block(block).end;
        loop {
            if cur < end && self.f.instr_op(cur) == Op::Goto {
                let target = self.f.goto_target(self.f.instr(cur)).ok_or(Fail)?;
                self.set_matched(cur);
                self.bind_label(label, target)?;
                return Ok(cur + 1);
            }
            if cur == end {
                let edges = &self.f.block(block).outgoing;
                if edges.len() != 1 || !edges[0].kind.is_unconditional() {
                    return Err(Fail);
                }
                let target = self.f.block(edges[0].target).start;
                self.bind_label(label, target)?;
                return Ok(cur);
            }
            if cur > end {
                return Err(Fail);
            }
            if self.is_extra_deleted(cur) {
                cur += 1;
                continue;
            }
            if !allow_kept && !self.absorb(cur) {
                return Err(Fail);
            }
            cur += 1;
        }
    }

    // -- driver -------------------------------------------------------------------
    fn run(&mut self, index: u32, pattern_index: usize) -> MResult<Match> {
        let blocks = &self.pattern.blocks;
        self.current_block = 0;
        self.match_block(&blocks[0], index, true, blocks.len() == 1)?;
        let mut visited = vec![false; blocks.len()];
        visited[0] = true;
        let mut progress = true;
        while progress {
            progress = false;
            for (i, pblock) in blocks.iter().enumerate() {
                if visited[i] {
                    continue;
                }
                let Some(label) = pblock.label else { continue };
                let Some(target) = self.labels[label.0 as usize] else { continue };
                self.current_block = i;
                self.match_block(pblock, target, false, i == blocks.len() - 1)?;
                visited[i] = true;
                progress = true;
            }
        }
        if let Some(i) = visited.iter().position(|v| !v) {
            let name = self.pattern.blocks[i].label.map(|l| self.pattern.label_name(l).to_string()).unwrap_or_default();
            return Err(self.why(|| format!("no branch of the code leads to the pattern's block {name}")));
        }
        let (deleted, kept) = self.post_checks().map_err(|_| {
            self.settle();
            Fail
        })?;
        let entry_first = self.entry_first.ok_or(Fail)?;
        let entry_last = self.entry_last.ok_or(Fail)?;
        let branch_target = match self.pattern.exit_branch() {
            Some(external) => Some(self.labels[external.0 as usize].ok_or(Fail)?),
            None => None,
        };
        let mut region_blocks: Vec<u32> = deleted.ones().map(|i| self.f.block_of(i as u32).start).collect();
        region_blocks.sort_unstable();
        region_blocks.dedup();
        let mut own_blocks: Vec<u32> = self.matched.ones().map(|i| self.f.block_of(i as u32).start).collect();
        own_blocks.sort_unstable();
        own_blocks.dedup();
        let mut internal: Vec<u32> = self.internal_blocks.iter().map(|b| self.f.block(*b).start).collect();
        internal.sort_unstable();
        Ok(Match {
            pattern: pattern_index,
            entry_index: entry_first,
            call_index: entry_last,
            deleted,
            region_blocks,
            own_blocks,
            internal_blocks: internal,
            exit_index: self.exit_index,
            exit_goto: self.exit_goto,
            bindings: self.bindings.clone(),
            labels: self.labels.clone(),
            kept,
            chased: self.chased.clone(),
            ret_size: self.ret_size,
            result_var: None,
            branch_target,
        })
    }

    // -- safety checks ---------------------------------------------------------------
    fn post_checks(&mut self) -> MResult<(InstrSet, Vec<u32>)> {
        let f = self.f;
        let env = self.env;
        let mut deleted = self.matched.clone();
        deleted.union_with(&self.absorbed_set);

        // Removed blocks may only be reachable from inside the region.
        let mut region_blocks = f.block_set();
        for i in self.matched.ones() {
            region_blocks.insert(f.block_id_of(i as u32).0 as usize);
        }
        for bid in &self.internal_blocks {
            for edge in &f.block(*bid).incoming {
                if !region_blocks.contains(edge.source.0 as usize) {
                    return Err(Fail);
                }
            }
        }

        // Variables the call (re)defines: the result, declared outputs, and
        // variables passed by address.  They may stay live after the region.
        let by_reference = self.pattern.reference_placeholders();
        let mut redefined = VarSet::with_capacity(f.vars.len());
        for name in self.pattern.output_placeholders().union(by_reference).iter() {
            if let Some(v) = self.binding(name).and_then(|b| b.redefined_var()) {
                redefined.insert(v.0 as usize);
            }
        }
        for v in &self.clobbered {
            redefined.insert(v.0 as usize); // register clobbers of a matched call: never a value anyone relies on
        }

        // Followed definitions go away when nothing else needs their value.
        let mut all_deleted = deleted.clone();
        all_deleted.union_with(self.extra_deleted);
        let mut changed = true;
        while changed {
            changed = false;
            for (d, var) in self.chased.clone() {
                if deleted.contains(d as usize) || self.extra_live.contains(var.0 as usize) {
                    continue;
                }
                if !env.uses_outside(f, d, &all_deleted, var) {
                    deleted.insert(d as usize);
                    all_deleted.insert(d as usize);
                    changed = true;
                }
            }
        }

        // Values the region defines (other than what the call redefines) must be dead afterwards.
        let mut written = VarSet::with_capacity(f.vars.len());
        for i in deleted.ones() {
            for var in f.vars_written(f.instr(i as u32)) {
                written.insert(var.0 as usize);
                if redefined.contains(var.0 as usize) {
                    continue;
                }
                if env.uses_outside(f, i as u32, &all_deleted, var) {
                    // A reader between the matched statements is inside the match, not
                    // after it, and is fixed differently: say which.
                    let window = self.entry_first.zip(self.entry_last);
                    let inside = window.and_then(|(first, last)| {
                        env.uses_of(f, i as u32, var, None).into_iter().find(|u| (first..=last).contains(u) && !all_deleted.contains(*u as usize))
                    });
                    if let Some(u) = inside {
                        let reason = reads_region_value(f, u, var);
                        return Err(self.why(|| reason));
                    }
                    let name = f.var_name(var).to_string();
                    return Err(self.why(|| format!("{name}, computed inside the region at {i}, is still read after it")));
                }
            }
        }

        // Arguments are evaluated at the call, so they may not depend on values
        // the region itself produces (the result variable excepted).  A region
        // may still overwrite an argument variable after the call, as inlined
        // code does when it reuses the object pointer for the data pointer, as
        // long as that value stays inside the region: no read outside it (checked
        // above) and no merge with it outside the region's own blocks.
        let arguments = self.pattern.argument_placeholders();
        let mut arg_vars = VarSet::with_capacity(f.vars.len());
        for name in &arguments {
            let binding = self.binding(*name).ok_or(Fail)?;
            if by_reference.contains(*name) {
                let has_address = matches!(binding, Binding::Var(_) | Binding::Global { object: true, .. })
                    || matches!(binding, Binding::Member(m) if matches!(m.kind, MemberKind::Var | MemberKind::Addr));
                if !has_address {
                    return Err(Fail); // only a variable (or a member of one) has an address
                }
                continue;
            }
            for v in binding.reads(f) {
                arg_vars.insert(v.0 as usize);
            }
        }
        // An absorbed assignment is gone with the region; an argument that read
        // its value would then be read at the call with a different one.
        for i in &self.absorbed {
            if f.vars_written(f.instr(*i)).iter().any(|v| arg_vars.contains(v.0 as usize)) {
                return Err(Fail);
            }
        }
        let entry_last = self.entry_last.ok_or(Fail)?;
        let entry_first = self.entry_first.ok_or(Fail)?;
        let entry_block = f.block_of(entry_last).id;
        let entry_start = f.block(entry_block).start;
        for i in deleted.ones() {
            let i = i as u32;
            for var in f.vars_written(f.instr(i)) {
                if !arg_vars.contains(var.0 as usize) || redefined.contains(var.0 as usize) {
                    continue;
                }
                if f.block_id_of(i) == entry_block && i <= entry_last {
                    return Err(Fail); // written before the call
                }
                let merges = env.merges_of(f, i, var, entry_last).ok_or(Fail)?;
                for m in merges {
                    let mb = f.block_id_of(m.block_start);
                    if !region_blocks.contains(mb.0 as usize) || m.block_start == entry_start {
                        return Err(Fail);
                    }
                }
            }
        }

        // Instructions left in place between the first matched statement and the
        // call site must not interfere with the pattern.
        let mut reads_d = VarSet::with_capacity(f.vars.len());
        let mut impure_deleted = false;
        for i in deleted.ones() {
            let instr = f.instr(i as u32);
            for v in f.vars_read(instr) {
                reads_d.insert(v.0 as usize);
            }
            let op = f.op(instr);
            if op.is_impure() && !matches!(op, Op::If | Op::Goto) {
                impure_deleted = true;
            }
        }
        let mut kept: Vec<u32> = Vec::new();
        for i in entry_first..=entry_last {
            if deleted.contains(i as usize) || self.is_extra_deleted(i) {
                continue;
            }
            kept.push(i);
            let instr = f.instr(i);
            // Next to a store or call the region removes, only an instruction that
            // touches no memory may stay (`x0 = &dtor` between a global's stores).
            if f.op(instr).is_impure() || (impure_deleted && f.touches_memory(instr)) {
                let what = between(f, i);
                return Err(self.why(|| format!("{what} cannot stay next to a call or store the region removes; add it to the pattern")));
            }
            if let Some(v) = f.vars_written(instr).into_iter().find(|v| reads_d.contains(v.0 as usize) || arg_vars.contains(v.0 as usize)) {
                let (what, name) = (between(f, i), f.var_name(v).to_string());
                return Err(self.why(|| format!("{what} overwrites {name}, which the region reads; add the instruction to the pattern")));
            }
            if let Some(v) = f.vars_read(instr).into_iter().find(|v| written.contains(v.0 as usize)) {
                let reason = reads_region_value(f, i, v);
                return Err(self.why(|| reason));
            }
        }

        // Everything the call reads must still hold its value at the call site:
        // between the point where an argument was observed and the call, nothing
        // that survives may overwrite a variable that argument reads.
        for name in &arguments {
            let Some(binding) = self.binding(*name) else { continue };
            let site = self.bind_site[name.0 as usize];
            if site < 0 || by_reference.contains(*name) {
                continue;
            }
            if writes_between(f, site as u32, entry_last, &binding.reads(f), &all_deleted) {
                return Err(Fail);
            }
        }
        Ok((deleted, kept))
    }
}

/// The characters a byte image spells once it is complete: the bytes from
/// `base` must be contiguous and hold `wanted` characters (or, when the count
/// is open, any run of them) followed by a terminator and nothing but padding
/// zeros.  None while stores are still missing.  Without `terminated` the run
/// is over: the image is the text as long as it holds no zero byte and, when
/// a count is bound, exactly that many characters.
fn image_text(pieces: &BTreeMap<i64, u8>, base: i64, wanted: Option<i64>, terminated: bool) -> MResult<Option<Vec<u8>>> {
    if !pieces.contains_key(&base) {
        return Ok(None);
    }
    let mut image: Vec<u8> = Vec::new();
    while let Some(b) = pieces.get(&(base + image.len() as i64)) {
        image.push(*b);
    }
    if !terminated {
        if image.contains(&0) || wanted.map(|w| image.len() as i64 != w).unwrap_or(false) {
            return Ok(None);
        }
        return Ok(Some(image));
    }
    let n = match wanted {
        None => match image.iter().position(|b| *b == 0) {
            Some(n) => n,
            None => return Ok(None),
        },
        Some(w) => {
            let n = w as usize;
            if image.len() < n + 1 {
                return Ok(None);
            }
            if image[..n].contains(&0) || image[n] != 0 {
                return Err(Fail);
            }
            n
        }
    };
    if image[n..].iter().any(|b| *b != 0) {
        return Err(Fail);
    }
    Ok(Some(image[..n].to_vec()))
}

/// `fnmatch`-style matching with `*`, `?` and `[...]`.
pub fn glob_match(pattern: &str, text: &str) -> bool {
    fn rec(p: &[char], t: &[char]) -> bool {
        match p.first() {
            None => t.is_empty(),
            Some('*') => (0..=t.len()).any(|k| rec(&p[1..], &t[k..])),
            Some('?') => !t.is_empty() && rec(&p[1..], &t[1..]),
            Some('[') => {
                let Some(close) = p.iter().position(|c| *c == ']') else {
                    return !t.is_empty() && t[0] == '[' && rec(&p[1..], &t[1..]);
                };
                let Some(&c) = t.first() else { return false };
                let set = &p[1..close];
                let (negate, set) = if set.first() == Some(&'!') { (true, &set[1..]) } else { (false, set) };
                let mut hit = false;
                let mut i = 0;
                while i < set.len() {
                    if i + 2 < set.len() && set[i + 1] == '-' {
                        if set[i] <= c && c <= set[i + 2] {
                            hit = true;
                        }
                        i += 3;
                    } else {
                        if set[i] == c {
                            hit = true;
                        }
                        i += 1;
                    }
                }
                hit != negate && rec(&p[close + 1..], &t[1..])
            }
            Some(c) => !t.is_empty() && t[0] == *c && rec(&p[1..], &t[1..]),
        }
    }
    let p: Vec<char> = pattern.chars().collect();
    let t: Vec<char> = text.chars().collect();
    rec(&p, &t)
}

/// Instruction indices that may execute between `start` (where a value was
/// observed) and `end` (where it is used) on some path from the one to the
/// other, both excluded.  A path that comes back to `start` observes the value
/// afresh, so nothing beyond that point counts: the blocks are those reachable
/// from `start`'s block without crossing it again that reach `end`'s block.
pub fn path_instructions(f: &Function, start: u32, end: u32) -> InstrSet {
    let mut out = f.instr_set();
    let sb = f.block_id_of(start);
    let eb = f.block_id_of(end);
    if sb == eb && start <= end {
        // Straight down the block; a path around a loop comes back through
        // `start` first and observes the value afresh.
        for i in start + 1..end {
            out.insert(i as usize);
        }
        return out;
    }
    let reach = |from: BlockId, forward: bool| -> BlockSet {
        let mut seen = f.block_set();
        let mut stack: Vec<BlockId> = if forward {
            f.block(from).outgoing.iter().map(|e| e.target).collect()
        } else {
            f.block(from).incoming.iter().map(|e| e.source).collect()
        };
        while let Some(b) = stack.pop() {
            if seen.contains(b.0 as usize) {
                continue;
            }
            seen.insert(b.0 as usize);
            if b == sb {
                continue; // the observation point: not crossed
            }
            if forward {
                stack.extend(f.block(b).outgoing.iter().map(|e| e.target));
            } else {
                stack.extend(f.block(b).incoming.iter().map(|e| e.source));
            }
        }
        seen
    };
    let fwd = reach(sb, true); // blocks reachable from start's block by at least one edge
    let bwd = reach(eb, false); // blocks that reach end's block by at least one edge
    if sb == eb && !fwd.contains(sb.0 as usize) {
        return out; // the use precedes the observation and no loop joins them
    }
    for b in &f.blocks {
        let in_fwd = fwd.contains(b.id.0 as usize) || b.id == sb;
        let in_bwd = bwd.contains(b.id.0 as usize) || b.id == eb;
        if !(in_fwd && in_bwd) {
            continue;
        }
        for i in b.start..b.end {
            if i == start || i == end {
                continue;
            }
            let ok = if b.id == sb && b.id == eb {
                i > start || i < end // around the loop: after the observation, before the use
            } else if b.id == sb {
                i > start
            } else if b.id == eb {
                i < end || bwd.contains(eb.0 as usize) // after the use only when a loop brings control back
            } else {
                true
            };
            if ok {
                out.insert(i as usize);
            }
        }
    }
    out
}

/// Whether an instruction that stays (not in `skip`) on a path between the
/// point where an argument was observed (`site`) and the call may overwrite
/// one of the variables the argument `reads`.
pub fn writes_between(f: &Function, site: u32, call: u32, reads: &[VarId], skip: &InstrSet) -> bool {
    let (a, b) = if site <= call { (site, call) } else { (call, site) };
    for i in path_instructions(f, a, b).ones() {
        if skip.contains(i) {
            continue;
        }
        if f.vars_written(f.instr(i as u32)).iter().any(|v| reads.contains(v)) {
            return true;
        }
    }
    false
}

/// Where an attempt to match got to, for explaining a failure.
#[derive(Clone, Debug, Default)]
pub struct Attempt {
    /// Statements matched before this one.
    pub matched: u32,
    /// The pattern block and statement being tried.
    pub block: usize,
    pub stmt: usize,
    /// The instruction it was tried against.
    pub instr: u32,
    pub reason: Option<String>,
}

#[derive(Clone, Debug, Default)]
pub struct Trace {
    matched: u32,
    current: Attempt,
    /// The attempt that got furthest.
    pub best: Attempt,
}

/// Why a pattern does not match at a start instruction: the furthest attempt.
#[derive(Clone, Debug)]
pub struct Explanation {
    pub start: u32,
    pub attempt: Attempt,
}

impl Explanation {
    /// The source line of the pattern statement the attempt failed at, when known.
    pub fn line(&self, pattern: &Pattern) -> Option<u32> {
        pattern.blocks.get(self.attempt.block).and_then(|b| b.stmt_lines.get(self.attempt.stmt)).copied()
    }
}

/// Try `patterns[pattern_index]` at `index`, explaining a failure.
pub fn explain_pattern_at(round: &Round, patterns: &[Pattern], pattern_index: usize, index: u32, rules: &[Rule]) -> Result<Match, Explanation> {
    let empty = no_instrs();
    let none = no_vars();
    let mut state = State::new(round, &patterns[pattern_index], &empty, &none, rules, Vec::new());
    state.trace = Some(Trace::default());
    match state.run(index, pattern_index) {
        Ok(m) => Ok(m),
        Err(Fail) => {
            state.settle();
            let trace = state.trace.take().unwrap_or_default();
            Err(Explanation { start: index, attempt: trace.best })
        }
    }
}

/// Try a pattern at every plausible start (those in `within` first, when
/// given), returning the match or the attempt that got furthest.
pub fn explain_pattern(round: &Round, patterns: &[Pattern], pattern_index: usize, rules: &[Rule], within: Option<&InstrSet>) -> Result<Match, Explanation> {
    let f = round.f;
    let pattern = &patterns[pattern_index];
    let allowed = start_ops(pattern, rules);
    let mut starts: Vec<u32> = (0..f.len() as u32).filter(|i| allowed.as_ref().is_none_or(|a| a.contains(f.instr_op(*i)))).collect();
    if let Some(region) = within {
        starts.sort_by_key(|i| !region.contains(*i as usize));
    }
    let mut best: Option<Explanation> = None;
    for start in starts {
        match explain_pattern_at(round, patterns, pattern_index, start, rules) {
            Ok(m) => return Ok(m),
            Err(e) => {
                let inside = within.is_none_or(|r| r.contains(start as usize));
                let better = match &best {
                    None => true,
                    Some(b) => {
                        let b_inside = within.is_none_or(|r| r.contains(b.start as usize));
                        (inside, e.attempt.matched) > (b_inside, b.attempt.matched)
                    }
                };
                if better {
                    best = Some(e);
                }
            }
        }
    }
    Err(best.unwrap_or(Explanation { start: 0, attempt: Attempt::default() }))
}

/// Match `pattern` (the `pattern_index`-th of the finder's list) with its entry
/// block starting at instruction `index`.
pub fn match_pattern_at(
    round: &Round,
    patterns: &[Pattern],
    pattern_index: usize,
    index: u32,
    extra_deleted: &InstrSet,
    extra_live: &VarSet,
    rules: &[Rule],
) -> Option<Match> {
    let mut state = State::new(round, &patterns[pattern_index], extra_deleted, extra_live, rules, Vec::new());
    state.run(index, pattern_index).ok()
}

/// Match one pattern expression against one hybrid node; returns the bindings
/// on success.  Handy for tests and diagnostics.
pub fn match_expression(
    round: &Round,
    pattern: &Pattern,
    pexpr: &Expr,
    node: &Node,
    use_index: u32,
    rules: &[Rule],
    facts: Vec<Fact>,
) -> Option<Vec<Option<Binding>>> {
    let empty = InstrSet::with_capacity(0);
    let no_vars = VarSet::with_capacity(0);
    let mut state = State::new(round, pattern, &empty, &no_vars, rules, facts);
    state.use_index = use_index as i32;
    state.match_expr(pexpr, node).ok()?;
    Some(state.bindings)
}

/// An instruction left in place between matched statements, quoted.
fn between(f: &Function, i: u32) -> String {
    format!("instruction {i} (`{}`) between the matched statements", crate::render::render_stmt(f, i, None))
}

/// Why instruction `i`, left between matched statements, cannot stay: it reads
/// `var`, a value the match computes; and how the pattern can take it in.
fn reads_region_value(f: &Function, i: u32, var: VarId) -> String {
    let output = f
        .vars_written(f.instr(i))
        .first()
        .map(|d| format!(", with a 'result:' line for ${} if it is read afterwards", f.var_name(*d)))
        .unwrap_or_default();
    format!("{} reads {}, which the region computes; add the instruction to the pattern{output}", between(f, i), f.var_name(var))
}

/// The operations a rule may turn into `op` (its right side's root), or None
/// when some rule's right side is a bare placeholder and anything may.
fn rewritable_to(op: Op, rules: &[Rule]) -> Option<OpSet> {
    let mut out = OpSet::default();
    for rule in rules {
        let Expr::Op(rhs) = &rule.rhs else { return None };
        if rhs.op == op {
            if let Some(l) = rule.lhs_op() {
                out.insert(l);
            }
        }
    }
    Some(out)
}

/// The MLIL operations the pattern's first statement can match, or None when
/// it cannot be told: a cheap test before building a matcher state.
pub fn start_ops(pattern: &Pattern, rules: &[Rule]) -> Option<OpSet> {
    let stmt = pattern.blocks.first()?.stmts.first()?;
    Some(match stmt {
        Stmt::SetVar { .. } => OpSet::of(&[Op::SetVar]),
        Stmt::Store { .. } => OpSet::of(&[Op::Store]),
        Stmt::Call(_) => OpSet::of(&[Op::Call, Op::SetVar]),
        Stmt::Intrinsic(_) => OpSet::of(&[Op::Intrinsic]),
        Stmt::Ret(_) => OpSet::of(&[Op::Ret, Op::Tailcall]),
        Stmt::Nop => OpSet::of(&[Op::Nop]),
        Stmt::If { .. } => OpSet::of(&[Op::If]),
        Stmt::Goto(_) => OpSet::of(&[Op::Goto]),
        Stmt::Expr(Expr::Op(o)) => {
            let mut set = rewritable_to(o.op, rules)?;
            set.insert(o.op);
            if let Some(flat) = o.op.flat_field_op() {
                set.insert(flat); // a field of a global
            }
            set
        }
        Stmt::Expr(_) => return None,
    })
}

/// The operations a node must have for the pattern's `value:` to match it (a
/// variable always may: its definition is looked at), or None.
pub fn value_ops(pattern: &Pattern, rules: &[Rule]) -> Option<OpSet> {
    match pattern.value.as_ref()? {
        Expr::Call(_) => Some(OpSet::of(&[Op::Var])),
        Expr::Op(o) => {
            let mut set = rewritable_to(o.op, rules)?;
            set.insert(o.op);
            if let Some(flat) = o.op.flat_field_op() {
                set.insert(flat); // a field of a global
            }
            set.insert(Op::Var);
            Some(set)
        }
        _ => None,
    }
}

/// Find non-overlapping matches of `patterns` in the round's function,
/// earliest first.  Matches never start inside `exclude_blocks` (block ids).
pub fn find_matches(round: &Round, patterns: &[Pattern], rules: &[Rule], exclude_blocks: Option<&BlockSet>) -> Vec<Match> {
    let f = round.f;
    let candidates: Vec<(usize, Option<OpSet>)> = patterns
        .iter()
        .enumerate()
        .filter(|(_, p)| p.value.is_none() && !p.is_rules())
        .map(|(i, p)| (i, start_ops(p, rules)))
        .collect();
    let mut matches: Vec<Match> = Vec::new();
    let mut taken = f.instr_set();
    let mut live = VarSet::with_capacity(f.vars.len());
    for block in &f.blocks {
        if exclude_blocks.map(|x| x.contains(block.id.0 as usize)).unwrap_or(false) {
            continue;
        }
        for index in block.start..block.end {
            if taken.contains(index as usize) {
                continue;
            }
            let op = f.instr_op(index);
            for (pi, allowed) in &candidates {
                if let Some(allowed) = allowed {
                    if !allowed.contains(op) {
                        continue;
                    }
                }
                let Some(m) = match_pattern_at(round, patterns, *pi, index, &taken, &live, rules) else { continue };
                if !m.deleted.is_disjoint(&taken) {
                    continue;
                }
                taken.union_with(&m.deleted);
                for v in m.arg_vars(&patterns[*pi], f) {
                    live.insert(v.0 as usize);
                }
                matches.push(m);
                break;
            }
        }
    }
    matches
}

/// The variables a set of matches passes as arguments, as a set.
pub fn arg_var_set(f: &Function, matches: &[Match], patterns: &[Pattern]) -> VarSet {
    let mut live = VarSet::with_capacity(f.vars.len());
    for m in matches {
        for v in m.arg_vars(&patterns[m.pattern], f) {
            live.insert(v.0 as usize);
        }
    }
    live
}

/// A convenient empty instruction set for callers with nothing to exclude.
pub fn no_instrs() -> InstrSet {
    InstrSet::with_capacity(0)
}

pub fn no_vars() -> VarSet {
    VarSet::with_capacity(0)
}

#[allow(dead_code)]
fn _assert_small(_: SmallVec<[VarId; 4]>) {}
