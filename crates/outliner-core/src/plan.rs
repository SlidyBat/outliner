//! The rewrite plan: what the host has to build in the new MLIL function, in
//! host-neutral terms.
//!
//! The plan follows the copy-based transformation the official workflow
//! examples use: every instruction that is not part of a matched region is
//! copied, `ret = target(args)` (plus a `goto` when the region spanned several
//! blocks) takes the place of each region, hoisted calls precede a fused
//! guard, and expression sites become calls into fresh variables.  The host
//! resolves widths, allocates the fresh variables and emits the expressions.

use std::collections::BTreeMap;

use crate::binding::{Binding, MemberBase, MemberKind, MemberRef};
use crate::fused::{FusedMatch, HoistedCall};
use crate::il::{BlockSet, ExprId, Function, InstrSet, VarId};
use crate::literals::data_size;
use crate::matcher::Match;
use crate::ops::Op;
use crate::pattern::{Expr, Pattern, RET};
use crate::sites::ExprSite;

/// A variable of the new function: one of the old function's, or one the host allocates.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PlanVar {
    Existing(VarId),
    Fresh(usize),
}

/// An expression to build.  Widths the host resolves: an operation without a
/// size takes its first sized operand's width (else the address size), a
/// variable read its variable's width, a constant without a size its parent's.
#[derive(Clone, Debug)]
pub enum Emit {
    /// The old expression, copied verbatim.
    Copy(ExprId),
    /// The old expression copied at pointer width: Binary Ninja sizes an address
    /// inside a structure access by the access width, which is wrong for an argument.
    CopyAddress(ExprId),
    Var(PlanVar),
    VarSized(PlanVar, u16),
    AddressOf(VarId),
    AddressOfField(VarId, i64),
    Const(Option<u16>, i64),
    /// A pointer constant at address width.
    ConstPtr(u64),
    /// Zero-extended constant data holding a string literal.
    ConstData { size: u16, value: u64 },
    /// `base + offset` at address width.
    PtrAdd(Box<Emit>, i64),
    Op { op: Op, size: Option<u16>, args: Vec<Emit> },
}

#[derive(Clone, Debug)]
pub struct EmitCall {
    /// The pattern whose function is called (the host knows its target address and type).
    pub pattern: usize,
    /// Output variables with their widths (0: the variable's own).
    pub outputs: Vec<(PlanVar, u16)>,
    pub args: Vec<Emit>,
}

#[derive(Clone, Debug)]
pub struct Assign {
    pub var: PlanVar,
    /// 0: the variable's own width.
    pub size: u16,
    pub value: Emit,
}

#[derive(Clone, Debug)]
pub struct BranchEmit {
    pub cond: Emit,
    /// Source instruction indices of the two targets.
    pub leave: u32,
    pub stay: u32,
}

#[derive(Clone, Debug)]
pub enum Action {
    /// A plain match: the call (located at `entry_index`), its result
    /// assignments, then the exit branch or a goto to `exit_goto` when the
    /// join is not the block emitted next.
    Outline { entry_index: u32, call: EmitCall, results: Vec<Assign>, branch: Option<BranchEmit>, exit_goto: Option<u32> },
    /// Expression sites inside the instruction: calls before it, then the
    /// instruction with `replacements`, or `whole` in its place.
    Sites { calls: Vec<EmitCall>, whole: Option<EmitCall>, replacements: BTreeMap<ExprId, PlanVar> },
    /// A fused guard: the hoisted calls, the assignments, then a goto to the
    /// kept arm when it is not the block emitted next.
    Fused { calls: Vec<EmitCall>, assignments: Vec<Assign>, goto: Option<u32> },
    /// The instruction copied with some sub-expressions replaced by variable reads.
    Replace { replacements: BTreeMap<ExprId, PlanVar> },
}

#[derive(Clone, Debug)]
pub struct FreshVar {
    pub pattern: usize,
    /// A site expression whose storage the variable may share.
    pub example: Option<ExprId>,
    pub name: String,
}

#[derive(Clone, Debug, Default)]
pub struct Plan {
    /// Per instruction index, what to emit instead of (or around) it.
    pub actions: BTreeMap<u32, Action>,
    /// Instructions not copied.
    pub skip: InstrSet,
    /// Blocks not emitted at all.
    pub removed_blocks: BlockSet,
    pub fresh: Vec<FreshVar>,
    /// Variables to give the return type of a pattern's function: (variable, pattern).
    pub retype: Vec<(VarId, usize)>,
    /// How many regions the plan outlines.
    pub count: usize,
}

impl Plan {
    pub fn is_empty(&self) -> bool {
        self.actions.is_empty()
    }
}

struct Names {
    counts: BTreeMap<String, usize>,
}

impl Names {
    fn fresh(&mut self, pattern: &Pattern) -> String {
        // The temporary is named after the function: its unqualified name, since
        // `std::string::data_1` is no variable name.
        let base = pattern.name.rsplit("::").next().unwrap_or(&pattern.name).to_string();
        let n = self.counts.entry(base.clone()).or_insert(0);
        *n += 1;
        format!("{base}_{n}")
    }
}

fn emit_member(m: &MemberRef) -> Emit {
    match (m.kind, m.base) {
        (MemberKind::Var | MemberKind::Addr, MemberBase::Var(v)) => Emit::AddressOfField(v, m.offset),
        (MemberKind::Ptr, MemberBase::Var(v)) => Emit::PtrAdd(Box::new(Emit::VarSized(PlanVar::Existing(v), 0)), m.offset),
        (_, MemberBase::Expr(e)) => Emit::PtrAdd(Box::new(Emit::CopyAddress(e)), m.offset),
        (_, MemberBase::Var(v)) => Emit::PtrAdd(Box::new(Emit::Var(PlanVar::Existing(v))), m.offset),
    }
}

/// An expression reading what a placeholder was bound to.
fn emit_binding(f: &Function, b: &Binding) -> Result<Emit, String> {
    Ok(match b {
        Binding::Expr { expr, address } => {
            if *address {
                Emit::CopyAddress(*expr)
            } else {
                Emit::Copy(*expr)
            }
        }
        Binding::Var(v) => Emit::Var(PlanVar::Existing(*v)),
        Binding::Addr(v) => Emit::AddressOf(*v),
        Binding::Member(m) => emit_member(m),
        Binding::Int { value, .. } => Emit::Const(Some(f.address_size as u16), *value as i64),
        Binding::Bytes { bytes, .. } => Emit::Const(Some(f.address_size as u16), crate::binding::bytes_to_i128(bytes).unwrap_or(0) as i64),
        // the address of a global, which the decompiler shows as `&g`
        Binding::Global { addr, object: false } => Emit::ConstPtr(*addr),
        Binding::Global { object: true, .. } => {
            return Err("a global object is passed by its address: write &$name in the result line".to_string())
        }
    })
}

/// The MLIL for a `result:` expression; the call (or `$ret`) inside it reads `value`.
fn emit_result(f: &Function, bindings: &[Option<Binding>], node: &Expr, value: PlanVar, call_width: u16) -> Result<Emit, String> {
    match node {
        Expr::Call(_) => Ok(Emit::VarSized(value, call_width)),
        Expr::Placeholder(p) if *p == RET => Ok(Emit::VarSized(value, call_width)),
        Expr::Placeholder(p) => {
            let b = bindings.get(p.0 as usize).and_then(|b| b.as_ref()).ok_or_else(|| "unbound placeholder in result".to_string())?;
            // A constant the code spelled takes the width of the operation it is used in.
            match b.const_value(f) {
                Some(value) if matches!(b, Binding::Int { .. } | Binding::Bytes { .. }) => Ok(Emit::Const(None, value as i64)),
                _ => emit_binding(f, b),
            }
        }
        Expr::Const(_) => Err("a bare constant needs an enclosing operation to give it a size".to_string()),
        Expr::Op(o) => {
            let mut args = Vec::with_capacity(o.args.len());
            for a in &o.args {
                args.push(match a {
                    Expr::Const(c) => Emit::Const(None, *c as i64),
                    other => emit_result(f, bindings, other, value, call_width)?,
                });
            }
            if args.len() > 5 {
                return Err("too many operands in result: expression".to_string());
            }
            Ok(Emit::Op { op: o.op, size: o.size, args })
        }
        other => Err(format!("unsupported node in result: {other:?}")),
    }
}

/// One argument of a `result:` call: a constant, a bound placeholder, the
/// address of one, or `const_data(v, n)`: the `n` characters packed in the
/// constant `v` is bound to, which the decompiler shows as a string literal.
fn emit_arg(f: &Function, bindings: &[Option<Binding>], arg: &Expr) -> Result<Emit, String> {
    let addr = f.address_size as u16;
    let binding_of = |p: &crate::pattern::PhId| bindings.get(p.0 as usize).and_then(|b| b.as_ref());
    match arg {
        Expr::Const(c) => Ok(Emit::Const(Some(addr), *c as i64)),
        Expr::Op(o) if o.op == Op::AddressOf => {
            let Some(Expr::Placeholder(p)) = o.args.first() else { return Err("bad &placeholder".into()) };
            match binding_of(p) {
                Some(Binding::Member(m)) => Ok(emit_member(m)),
                Some(Binding::Var(v)) => Ok(Emit::AddressOf(*v)),
                Some(Binding::Addr(v)) => Ok(Emit::AddressOf(*v)),
                Some(Binding::Global { addr, object: true }) => Ok(Emit::ConstPtr(*addr)),
                _ => Err("an &placeholder needs a variable".into()),
            }
        }
        Expr::Op(o) if o.op == Op::ConstData => {
            let (source, length) = (&o.args[0], &o.args[1]);
            let (value, origin) = match source {
                Expr::Const(c) => (Some(*c), None),
                Expr::Placeholder(p) => {
                    let b = binding_of(p).ok_or("const_data needs its placeholder bound")?;
                    (b.const_value(f), b.origin())
                }
                _ => (None, None),
            };
            let chars = match length {
                Expr::Const(c) => Some(*c),
                Expr::Placeholder(p) => binding_of(p).and_then(|b| b.const_value(f)),
                _ => None,
            };
            let chars = chars.ok_or("const_data needs a constant count")?;
            if chars > 8 {
                // More text than a register holds: the matcher only binds such a literal
                // when the stores read it from the binary, so point at that copy.
                let origin = origin.ok_or("a literal of more than eight characters needs the binary's copy of it")?;
                return Ok(Emit::ConstPtr(origin));
            }
            let value = value.ok_or("const_data needs its placeholder bound to a constant")?;
            let size = data_size(chars as usize).ok_or("literal too long for register-sized constant data")?;
            let mask = if chars >= 16 { u128::MAX } else { (1u128 << (8 * chars as u32)) - 1 };
            Ok(Emit::ConstData { size, value: ((value as u128) & mask) as u64 })
        }
        Expr::Op(_) => emit_result(f, bindings, arg, PlanVar::Existing(VarId(0)), addr),
        Expr::Placeholder(p) => emit_binding(f, binding_of(p).ok_or("unbound argument")?),
        _ => Err("bad argument in result".into()),
    }
}

fn direct_output(m: &Match, pattern: &Pattern, f: &Function) -> bool {
    m.ret_var(f).is_some() && pattern.ret_is_call()
}

/// Build the plan for one round: `matches`, `fused` and `sites` are what the
/// finders found; `has_target[p]` says whether pattern `p` has a call target.
/// Errors are reported per pattern name.
pub fn build_plan(
    f: &Function,
    patterns: &[Pattern],
    matches: &[Match],
    fused: &[FusedMatch],
    sites: &[ExprSite],
    has_target: &[bool],
    retype_result: bool,
) -> Result<Plan, String> {
    let mut plan = Plan { skip: f.instr_set(), removed_blocks: f.block_set(), ..Default::default() };
    let mut names = Names { counts: BTreeMap::new() };
    let addr = f.address_size as u16;
    let mut fresh_calls: Vec<(usize, Option<ExprId>)> = Vec::new();
    let mut alloc = |pattern: usize, example: Option<ExprId>, plan: &mut Plan| -> PlanVar {
        let name = names.fresh(&patterns[pattern]);
        plan.fresh.push(FreshVar { pattern, example, name });
        fresh_calls.push((pattern, example));
        PlanVar::Fresh(plan.fresh.len() - 1)
    };

    // -- plain matches --------------------------------------------------------------
    struct Pending<'m> {
        m: &'m Match,
        value: Option<PlanVar>,
    }
    let mut pending: Vec<Pending> = Vec::new();
    for m in matches {
        let pattern = &patterns[m.pattern];
        if !has_target[m.pattern] {
            continue;
        }
        let value = if !pattern.results.is_empty() && pattern.returns && !direct_output(m, pattern, f) {
            // No code variable receives the call's own value: give it a fresh one.
            Some(alloc(m.pattern, None, &mut plan))
        } else {
            None
        };
        plan.skip.union_with(&m.deleted);
        for start in &m.internal_blocks {
            if let Some(b) = f.block_at(*start) {
                plan.removed_blocks.insert(b.id.0 as usize);
            }
        }
        pending.push(Pending { m, value });
    }
    for fm in fused {
        if fm.calls.iter().any(|c| !has_target[c.pattern]) {
            continue;
        }
        plan.skip.union_with(&fm.deleted);
        for start in &fm.removed_blocks {
            if let Some(b) = f.block_at(*start) {
                plan.removed_blocks.insert(b.id.0 as usize);
            }
        }
    }
    for site in sites {
        if has_target[site.pattern] {
            plan.skip.union_with(&site.deleted);
        }
    }

    // The block that will be emitted right after each block, so that a goto to
    // it can be left out (control falls through in the new function).
    let mut next_emitted: BTreeMap<u32, Option<u32>> = BTreeMap::new();
    let mut following: Option<u32> = None;
    for b in f.blocks.iter().rev() {
        next_emitted.insert(b.start, following);
        if !plan.removed_blocks.contains(b.id.0 as usize) {
            following = Some(b.start);
        }
    }
    let next_after = |index: u32| -> Option<u32> { next_emitted.get(&f.block_of(index).start).copied().flatten() };

    for Pending { m, value } in pending {
        let pattern = &patterns[m.pattern];
        let ret_var = m.ret_var(f);
        let action = match pattern.result_call() {
            None => {
                let mut args = Vec::new();
                for id in pattern.param_ids() {
                    let id = id.ok_or_else(|| format!("{}: a parameter has no binding", pattern.name))?;
                    let b = m.binding(id).ok_or_else(|| format!("{}: unbound parameter", pattern.name))?;
                    args.push(emit_binding(f, b).map_err(|e| format!("{}: {e}", pattern.name))?);
                }
                let mut outputs = Vec::new();
                if pattern.returns {
                    if let Some(v) = ret_var {
                        outputs.push((PlanVar::Existing(v), m.ret_size));
                    }
                }
                let exit_goto = m.exit_goto.then_some(m.exit_index).flatten().filter(|e| next_after(m.call_index) != Some(*e));
                Action::Outline { entry_index: m.entry_index, call: EmitCall { pattern: m.pattern, outputs, args }, results: Vec::new(), branch: None, exit_goto }
            }
            Some(call) => {
                // result: lines fix the argument list; the call's value goes to the code's
                // $ret variable when that is what it holds, else to a fresh variable, and
                // every other declared output is computed from it afterwards.
                let mut args = Vec::new();
                for a in &call.args {
                    args.push(emit_arg(f, &m.bindings, a).map_err(|e| format!("{}: {e}", pattern.name))?);
                }
                if !pattern.returns {
                    let exit_goto = m.exit_goto.then_some(m.exit_index).flatten().filter(|e| next_after(m.call_index) != Some(*e));
                    let branch = None;
                    Action::Outline { entry_index: m.entry_index, call: EmitCall { pattern: m.pattern, outputs: Vec::new(), args }, results: Vec::new(), branch, exit_goto }
                } else {
                    let direct = direct_output(m, pattern, f);
                    let (value_var, width) = if direct {
                        (PlanVar::Existing(ret_var.unwrap()), m.ret_size)
                    } else {
                        (value.expect("a fresh variable for the call's value"), 0)
                    };
                    let mut results = Vec::new();
                    for (name, expr) in &pattern.results {
                        if *name == RET && (direct || ret_var.is_none()) {
                            continue;
                        }
                        let Some(Binding::Var(v)) = m.binding(*name) else { continue };
                        let value_emit = emit_result(f, &m.bindings, expr, value_var, width).map_err(|e| format!("{}: {e}", pattern.name))?;
                        let size = if *name == RET { m.ret_size } else { 0 };
                        results.push(Assign { var: PlanVar::Existing(*v), size, value: value_emit });
                    }
                    let mut branch = None;
                    if let (Some(cond), Some(leave), Some(stay)) = (&pattern.branch, m.branch_target, m.exit_index) {
                        // The pattern left through a branch: take it after the call when branch: holds.
                        let cond = emit_result(f, &m.bindings, cond, value_var, width).map_err(|e| format!("{}: {e}", pattern.name))?;
                        branch = Some(BranchEmit { cond, leave, stay });
                    }
                    let exit_goto = if pattern.branch.is_some() {
                        None // the exit branch emitted with the call already leads on
                    } else {
                        m.exit_goto.then_some(m.exit_index).flatten().filter(|e| next_after(m.call_index) != Some(*e))
                    };
                    Action::Outline {
                        entry_index: m.entry_index,
                        call: EmitCall { pattern: m.pattern, outputs: vec![(value_var, width)], args },
                        results,
                        branch,
                        exit_goto,
                    }
                }
            }
        };
        plan.actions.insert(m.call_index, action);
        plan.count += 1;
        if retype_result && (pattern.results.is_empty() || direct_output(m, pattern, f)) && pattern.returns {
            if let Some(v) = ret_var {
                plan.retype.push((v, m.pattern));
            }
        }
    }

    // -- fused guards --------------------------------------------------------------
    let mut replacements: BTreeMap<u32, BTreeMap<ExprId, PlanVar>> = BTreeMap::new();
    for fm in fused {
        if fm.calls.iter().any(|c| !has_target[c.pattern]) {
            continue;
        }
        let mut calls = Vec::new();
        let mut vars: Vec<Option<PlanVar>> = Vec::new();
        for call in &fm.calls {
            let pattern = &patterns[call.pattern];
            let var = if pattern.returns { Some(alloc(call.pattern, call.example, &mut plan)) } else { None };
            vars.push(var);
            calls.push(emit_hoisted(f, pattern, call, var).map_err(|e| format!("{}: {e}", pattern.name))?);
        }
        for (i, repl) in &fm.replacements {
            let entry = replacements.entry(*i).or_default();
            for (e, k) in repl {
                if let Some(v) = vars[*k] {
                    entry.insert(*e, v);
                }
            }
        }
        let assignments = fm
            .assignments
            .iter()
            .filter_map(|(var, k)| vars[*k].map(|v| Assign { var: PlanVar::Existing(*var), size: 0, value: Emit::Var(v) }))
            .collect();
        let goto = if next_after(fm.guard_index) != Some(fm.kept_block) { Some(fm.kept_block) } else { None };
        plan.actions.insert(fm.guard_index, Action::Fused { calls, assignments, goto });
        plan.count += 1;
    }

    // -- expression sites ------------------------------------------------------------
    let mut site_actions: BTreeMap<u32, (Vec<EmitCall>, Option<EmitCall>)> = BTreeMap::new();
    for site in sites {
        if !has_target[site.pattern] {
            continue;
        }
        let pattern = &patterns[site.pattern];
        let var = if site.whole_rhs {
            PlanVar::Existing(site.dest.ok_or_else(|| format!("{}: a whole-rhs site without a variable", pattern.name))?)
        } else {
            let v = alloc(site.pattern, Some(site.expr), &mut plan);
            replacements.entry(site.instr_index).or_default().insert(site.expr, v);
            v
        };
        let mut args = Vec::new();
        for id in pattern.param_ids() {
            let id = id.ok_or_else(|| format!("{}: a parameter has no binding", pattern.name))?;
            let b = site.binding(id).ok_or_else(|| format!("{}: unbound parameter", pattern.name))?;
            args.push(emit_binding(f, b).map_err(|e| format!("{}: {e}", pattern.name))?);
        }
        let size = if site.whole_rhs { site.size } else { 0 };
        let call = EmitCall { pattern: site.pattern, outputs: vec![(var, size)], args };
        let entry = site_actions.entry(site.instr_index).or_default();
        if site.whole_rhs {
            entry.1 = Some(call);
            if retype_result {
                if let Some(d) = site.dest {
                    plan.retype.push((d, site.pattern));
                }
            }
        } else {
            entry.0.push(call);
        }
        plan.count += 1;
    }
    for (index, (calls, whole)) in site_actions {
        let repl = replacements.remove(&index).unwrap_or_default();
        plan.actions.insert(index, Action::Sites { calls, whole, replacements: repl });
    }
    for (index, repl) in replacements {
        if let Some(Action::Fused { .. }) = plan.actions.get(&index) {
            continue; // the guard itself is replaced, its replacements are moot
        }
        plan.actions.entry(index).or_insert(Action::Replace { replacements: repl });
    }
    let _ = addr;
    Ok(plan)
}

/// A call hoisted above a fused guard: its arguments as the pattern's
/// `result:` line spells them, or the parameters' bindings.
fn emit_hoisted(f: &Function, pattern: &Pattern, call: &HoistedCall, var: Option<PlanVar>) -> Result<EmitCall, String> {
    let args = match pattern.result_call() {
        Some(rc) => rc.args.iter().map(|a| emit_arg(f, &call.bindings, a)).collect::<Result<Vec<_>, _>>()?,
        None => {
            let mut args = Vec::new();
            for id in pattern.param_ids() {
                let id = id.ok_or("a parameter has no binding")?;
                args.push(emit_binding(f, call.binding(id).ok_or("unbound parameter")?)?);
            }
            args
        }
    };
    let outputs = var.map(|v| vec![(v, 0)]).unwrap_or_default();
    Ok(EmitCall { pattern: call.pattern, outputs, args })
}
