//! Outline inlined calls that the compiler fused under a shared guard.
//!
//! When two inlined accessors test the same predicate (libc++'s "is the
//! string long" flag), the compiler tests it once and specialises everything
//! below it per arm, often duplicating the code that follows.  Nothing in the
//! result looks like a call any more; each accessor exists only as one value
//! per path.
//!
//! This module recognises that situation: an `if` whose two arms are
//! isomorphic except for pairs of expressions that a *pure* guarded-value
//! pattern explains (`e_true` is the pattern's true arm, `e_false` its false
//! arm, under the same guard and the same arguments).  The rewrite hoists one
//! call per explained value above the guard, substitutes it into the true
//! arm, and drops the false arm and the guard itself.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use crate::binding::Binding;
use crate::hybrid::{complement_of, instantiate, Fail, MResult, Node};
use crate::il::{BlockId, BlockSet, ExprId, Function, InstrSet, Operand, VarId};
use crate::matcher::{writes_between, Round, State, VarSet};
use crate::ops::Op;
use crate::pattern::{negate, Expr, Pattern, Rule, Stmt};

#[derive(Clone, Debug)]
pub struct HoistedCall {
    pub pattern: usize,
    pub bindings: Vec<Option<Binding>>,
    pub chased: Vec<(u32, VarId)>,
    /// A site expression, used to pick storage for the fresh variable.
    pub example: Option<ExprId>,
    pub bind_site: Vec<i32>,
    /// Fresh variable, assigned by the planner.
    pub var: Option<VarId>,
}

impl HoistedCall {
    pub fn binding(&self, id: crate::pattern::PhId) -> Option<&Binding> {
        self.bindings.get(id.0 as usize).and_then(|b| b.as_ref())
    }
}

#[derive(Clone, Debug)]
pub struct FusedMatch {
    pub guard_index: u32,
    /// Start of the guard's block.
    pub guard_block: u32,
    /// Start of the arm that stays.
    pub kept_block: u32,
    /// Start of the arm that goes.
    pub removed_block: u32,
    pub kept_blocks: Vec<u32>,
    pub removed_blocks: Vec<u32>,
    pub deleted: InstrSet,
    pub calls: Vec<HoistedCall>,
    /// instruction index -> {expression: index into calls}
    pub replacements: BTreeMap<u32, BTreeMap<ExprId, usize>>,
    pub blocks_touched: Vec<u32>,
    /// The kept arm is the guard's true target.
    pub kept_is_true: bool,
    /// (variable, index into calls): assignments to make after the hoisted calls,
    /// re-establishing a value the removed arm set and code after the join reads.
    pub assignments: Vec<(VarId, usize)>,
}

impl FusedMatch {
    pub fn entry_index(&self) -> u32 {
        self.guard_index
    }

    pub fn deleted_sorted(&self) -> Vec<u32> {
        self.deleted.ones().map(|i| i as u32).collect()
    }
}

fn masked(value: i128, size: u16) -> i128 {
    if size > 0 && size < 16 {
        value & ((1i128 << (8 * size as u32)) - 1)
    } else {
        value
    }
}

// --------------------------------------------------------------------------- dominators

/// Dominator sets by block id (the entry is the first block).
pub fn compute_dominators(f: &Function) -> Vec<BlockSet> {
    let n = f.blocks.len();
    let mut dom: Vec<BlockSet> = Vec::with_capacity(n);
    if n == 0 {
        return dom;
    }
    let mut all = f.block_set();
    all.insert_range(..);
    for b in &f.blocks {
        if b.id.0 == 0 {
            let mut only = f.block_set();
            only.insert(0);
            dom.push(only);
        } else {
            dom.push(all.clone());
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for b in f.blocks.iter().skip(1) {
            let preds: Vec<BlockId> = b.incoming.iter().map(|e| e.source).collect();
            let mut new = all.clone();
            for p in &preds {
                new.intersect_with(&dom[p.0 as usize]);
            }
            new.insert(b.id.0 as usize);
            if preds.is_empty() {
                new = f.block_set();
                new.insert(b.id.0 as usize);
            }
            if new != dom[b.id.0 as usize] {
                dom[b.id.0 as usize] = new;
                changed = true;
            }
        }
    }
    dom
}

// --------------------------------------------------------------------------- guard candidates

#[derive(Clone)]
struct Candidate {
    pattern: usize,
    bindings: Vec<Option<Binding>>,
    /// Pattern guard is the negation of the site guard.
    swap: bool,
    chased: Vec<(u32, VarId)>,
    bind_site: Vec<i32>,
    /// The pattern guard instantiated with the bindings.
    guard: Node,
    /// The site condition as the pattern was matched against it.
    form: Node,
    /// `form` has the pattern guard's polarity (not its negation's).
    form_direct: bool,
}

/// Pure guarded-value patterns whose guard (possibly negated) matches the
/// site's condition (or its complement), structurally or through the rewrite rules.
fn guard_candidates(round: &Round, patterns: &[Pattern], pure: &[usize], guard_index: u32, cond: ExprId, rules: &[Rule]) -> Vec<Candidate> {
    let f = round.f;
    let mut result = Vec::new();
    let cond_node = Node::Expr(cond);
    let complement = complement_of(f, &cond_node);
    let empty = f.instr_set();
    let no_vars = VarSet::with_capacity(f.vars.len());
    for pi in pure {
        let pattern = &patterns[*pi];
        let guard: &Expr = match pattern.guarded_value() {
            Some(gv) => {
                if !pattern.pure {
                    continue;
                }
                &gv.guard
            }
            None => match pattern.guarded_statements() {
                Some(gs) => &gs.guard,
                None => continue,
            },
        };
        let negated = negate(guard);
        let mut attempts: Vec<(bool, Option<&Expr>, &Node, bool)> = vec![(false, Some(guard), &cond_node, true), (true, negated.as_ref(), &cond_node, false)];
        if let Some(c) = &complement {
            attempts.push((true, Some(guard), c, true));
            attempts.push((false, negated.as_ref(), c, false));
        }
        for (swap, guard_expr, node, direct) in attempts {
            let Some(guard_expr) = guard_expr else { continue };
            let mut state = State::new(round, pattern, &empty, &no_vars, rules, Vec::new());
            state.use_index = guard_index as i32;
            let outcome = state.match_expr(guard_expr, node).and_then(|form| {
                let g = instantiate(guard, &state.bindings, &state.bind_site)?;
                Ok((form, g))
            });
            state.use_index = -1;
            let Ok((form, g)) = outcome else { continue };
            result.push(Candidate {
                pattern: *pi,
                bindings: state.bindings.clone(),
                swap,
                chased: state.chased.clone(),
                bind_site: state.bind_site.clone(),
                guard: g,
                form,
                form_direct: direct,
            });
            break;
        }
    }
    result
}

// --------------------------------------------------------------------------- isomorphism

#[derive(Clone)]
struct IsoSnapshot {
    block_map: HashMap<BlockId, BlockId>,
    var_map: HashMap<VarId, VarId>,
    var_map_rev: HashMap<VarId, VarId>,
    calls: Vec<HoistedCall>,
    replacements: BTreeMap<u32, BTreeMap<ExprId, usize>>,
    queue: VecDeque<(BlockId, BlockId)>,
    extras_k: BTreeMap<u32, u32>,
    extras_r: BTreeSet<u32>,
    runs: Vec<(u32, usize, u32, usize, usize)>,
}

/// Isomorphism between the arm that stays ("kept") and the arm that goes
/// ("removed"), modulo value pairs a pure pattern explains.
struct Iso<'a> {
    round: &'a Round<'a>,
    f: &'a Function,
    patterns: &'a [Pattern],
    candidates: &'a [Candidate],
    rules: &'a [Rule],
    /// Blocks dominated by the kept arm (including it).
    kept: &'a BlockSet,
    removed: &'a BlockSet,
    kept_is_true: bool,
    block_map: HashMap<BlockId, BlockId>,
    var_map: HashMap<VarId, VarId>,
    var_map_rev: HashMap<VarId, VarId>,
    /// kept-side extra -> removed-side context index
    extras_k: BTreeMap<u32, u32>,
    extras_r: BTreeSet<u32>,
    calls: Vec<HoistedCall>,
    replacements: BTreeMap<u32, BTreeMap<ExprId, usize>>,
    queue: VecDeque<(BlockId, BlockId)>,
    t_start: Option<BlockId>,
    f_start: Option<BlockId>,
    /// Statement runs at the arm starts a void pattern stands for:
    /// (kept start, kept count, removed start, removed count, index into calls)
    runs: Vec<(u32, usize, u32, usize, usize)>,
    /// Variables written inside each arm: only those may be renamed between the arms.
    local_k: VarSet,
    local_r: VarSet,
    /// Variables an arm defines and code after the arms reads: paired only with themselves.
    escaping_k: VarSet,
    escaping_r: VarSet,
}

impl<'a> Iso<'a> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        round: &'a Round<'a>,
        patterns: &'a [Pattern],
        candidates: &'a [Candidate],
        rules: &'a [Rule],
        kept: &'a BlockSet,
        removed: &'a BlockSet,
        kept_is_true: bool,
    ) -> Iso<'a> {
        let f = round.f;
        let mut iso = Iso {
            round,
            f,
            patterns,
            candidates,
            rules,
            kept,
            removed,
            kept_is_true,
            block_map: HashMap::new(),
            var_map: HashMap::new(),
            var_map_rev: HashMap::new(),
            extras_k: BTreeMap::new(),
            extras_r: BTreeSet::new(),
            calls: Vec::new(),
            replacements: BTreeMap::new(),
            queue: VecDeque::new(),
            t_start: None,
            f_start: None,
            runs: Vec::new(),
            local_k: VarSet::with_capacity(f.vars.len()),
            local_r: VarSet::with_capacity(f.vars.len()),
            escaping_k: VarSet::with_capacity(f.vars.len()),
            escaping_r: VarSet::with_capacity(f.vars.len()),
        };
        iso.local_k = iso.written_in(kept);
        iso.local_r = iso.written_in(removed);
        iso.escaping_k = iso.escaping(kept);
        iso.escaping_r = iso.escaping(removed);
        iso
    }

    fn written_in(&self, blocks: &BlockSet) -> VarSet {
        let mut out = VarSet::with_capacity(self.f.vars.len());
        for b in blocks.ones() {
            for i in self.f.block(BlockId(b as u32)).range() {
                for v in self.f.vars_written(self.f.instr(i)) {
                    out.insert(v.0 as usize);
                }
            }
        }
        out
    }

    fn escaping(&self, blocks: &BlockSet) -> VarSet {
        let mut region = self.f.instr_set();
        for b in blocks.ones() {
            for i in self.f.block(BlockId(b as u32)).range() {
                region.insert(i as usize);
            }
        }
        let mut out = VarSet::with_capacity(self.f.vars.len());
        for i in region.ones() {
            for var in self.f.vars_written(self.f.instr(i as u32)) {
                if self.round.env.uses_outside(self.f, i as u32, &region, var) {
                    out.insert(var.0 as usize);
                }
            }
        }
        out
    }

    // -- state rollback for instruction-level attempts ------------------------
    fn snapshot(&self) -> IsoSnapshot {
        IsoSnapshot {
            block_map: self.block_map.clone(),
            var_map: self.var_map.clone(),
            var_map_rev: self.var_map_rev.clone(),
            calls: self.calls.clone(),
            replacements: self.replacements.clone(),
            queue: self.queue.clone(),
            extras_k: self.extras_k.clone(),
            extras_r: self.extras_r.clone(),
            runs: self.runs.clone(),
        }
    }

    fn restore(&mut self, snap: IsoSnapshot) {
        self.block_map = snap.block_map;
        self.var_map = snap.var_map;
        self.var_map_rev = snap.var_map_rev;
        self.calls = snap.calls;
        self.replacements = snap.replacements;
        self.queue = snap.queue;
        self.extras_k = snap.extras_k;
        self.extras_r = snap.extras_r;
        self.runs = snap.runs;
    }

    // -- variables -------------------------------------------------------------
    fn map_var(&mut self, vt: VarId, vf: VarId) -> MResult<()> {
        if vt == vf {
            if self.var_map.get(&vt).map(|m| *m != vf).unwrap_or(false) {
                return Err(Fail);
            }
            return Ok(());
        }
        if !self.local_k.contains(vt.0 as usize) || !self.local_r.contains(vf.0 as usize) {
            return Err(Fail); // a value from outside the arms cannot be "renamed"
        }
        if self.escaping_k.contains(vt.0 as usize) || self.escaping_r.contains(vf.0 as usize) {
            return Err(Fail); // read after the join under its own name: no renaming happens there
        }
        if let Some(m) = self.var_map.get(&vt) {
            if *m != vf {
                return Err(Fail);
            }
            return Ok(());
        }
        if self.var_map_rev.contains_key(&vf) {
            return Err(Fail);
        }
        self.var_map.insert(vt, vf);
        self.var_map_rev.insert(vf, vt);
        Ok(())
    }

    // -- blocks ----------------------------------------------------------------
    fn run(&mut self, t_start: BlockId, f_start: BlockId) -> MResult<()> {
        self.t_start = Some(t_start);
        self.f_start = Some(f_start);
        self.queue.push_back((t_start, f_start));
        while let Some((t, f)) = self.queue.pop_front() {
            if let Some(m) = self.block_map.get(&t) {
                if *m != f {
                    return Err(Fail);
                }
                continue;
            }
            self.block_map.insert(t, f);
            self.cmp_block(t, f)?;
        }
        Ok(())
    }

    fn cmp_block(&mut self, bt: BlockId, bf: BlockId) -> MResult<()> {
        let (ts, te) = (self.f.block(bt).start, self.f.block(bt).end);
        let (fs, fe) = (self.f.block(bf).start, self.f.block(bf).end);
        let (mut i, mut j) = (ts, fs);
        if Some(bt) == self.t_start && Some(bf) == self.f_start {
            if let Some((ck, cr)) = self.explain_run(bt, bf) {
                i += ck as u32;
                j += cr as u32;
            }
        }
        while i < te || j < fe {
            if i < te && j < fe && self.try_cmp_instr(i, j) {
                i += 1;
                j += 1;
                continue;
            }
            if i < te && self.is_extra(i) {
                let ctx = if fe > fs { j.min(fe - 1) } else { fs };
                self.extras_k.insert(i, ctx);
                i += 1;
                continue;
            }
            if j < fe && self.is_extra(j) {
                self.extras_r.insert(j);
                j += 1;
                continue;
            }
            return Err(Fail);
        }
        // Blocks ending in a branch had their targets paired by the instruction
        // comparison (possibly inverted); only fall-through edges remain to pair.
        let terminated = |b: BlockId| -> bool {
            let blk = self.f.block(b);
            blk.end > blk.start && matches!(self.f.instr_op(blk.end - 1), Op::If | Op::Goto)
        };
        if terminated(bt) != terminated(bf) {
            return Err(Fail);
        }
        if !terminated(bt) {
            let et = self.f.block(bt).outgoing.clone();
            let ef = self.f.block(bf).outgoing.clone();
            if et.len() != ef.len() || et.len() > 1 {
                return Err(Fail);
            }
            for (a, b) in et.iter().zip(&ef) {
                if a.kind != b.kind {
                    return Err(Fail);
                }
                self.map_target(self.f.block(a.target).start, self.f.block(b.target).start)?;
            }
        }
        Ok(())
    }

    /// The block `start` really continues at: compilers sometimes reach a
    /// shared target through a block holding nothing but a goto, in one arm
    /// and not the other.
    fn through_gotos(&self, mut start: u32) -> u32 {
        let mut seen: Vec<u32> = Vec::new();
        while !seen.contains(&start) {
            seen.push(start);
            let Some(block) = self.f.block_at(start) else { break };
            if block.end - block.start != 1 || self.f.instr_op(block.start) != Op::Goto {
                break;
            }
            match self.f.goto_target(self.f.instr(block.start)) {
                Some(t) => start = t,
                None => break,
            }
        }
        start
    }

    fn block_id(&self, start: u32) -> Option<BlockId> {
        self.f.block_at(start).map(|b| b.id)
    }

    fn map_target(&mut self, tau: u32, phi: u32) -> MResult<()> {
        let (tau, phi) = (self.through_gotos(tau), self.through_gotos(phi));
        let tau_id = self.block_id(tau).ok_or(Fail)?;
        let phi_id = self.block_id(phi).ok_or(Fail)?;
        if self.kept.contains(tau_id.0 as usize) {
            if !self.removed.contains(phi_id.0 as usize) {
                return Err(Fail);
            }
            match self.block_map.get(&tau_id) {
                Some(m) => {
                    if *m != phi_id {
                        return Err(Fail);
                    }
                }
                None => self.queue.push_back((tau_id, phi_id)),
            }
        } else if phi != tau || self.removed.contains(phi_id.0 as usize) {
            return Err(Fail);
        }
        Ok(())
    }

    fn is_extra(&self, i: u32) -> bool {
        let op = self.f.instr_op(i);
        op == Op::SetVar && !op.is_impure()
    }

    // -- instructions ------------------------------------------------------------
    fn try_cmp_instr(&mut self, i: u32, j: u32) -> bool {
        let snap = self.snapshot();
        match self.cmp_instr(i, j) {
            Ok(()) => true,
            Err(Fail) => {
                self.restore(snap);
                false
            }
        }
    }

    fn replaced_count(&self) -> usize {
        self.replacements.values().map(|r| r.len()).sum()
    }

    fn cmp_instr(&mut self, i: u32, j: u32) -> MResult<()> {
        let f = self.f;
        let (t, fe) = (f.instr(i), f.instr(j));
        if f.op(t) != f.op(fe) {
            return Err(Fail);
        }
        if f.op(t) == Op::If {
            return self.cmp_if(t, fe, i, j);
        }
        let before = self.replaced_count();
        let (ot, of) = (f.operands(t).to_vec(), f.operands(fe).to_vec());
        if ot.len() != of.len() {
            return Err(Fail);
        }
        let is_branch = matches!(f.op(t), Op::If | Op::Goto);
        for (a, b) in ot.iter().zip(&of) {
            match (a, b) {
                (Operand::Expr(x), Operand::Expr(y)) => self.cmp_expr(*x, &Node::Expr(*y), i, j, false)?,
                (Operand::List { .. }, Operand::List { .. }) => {
                    let (la, lb) = (f.list(*a).to_vec(), f.list(*b).to_vec());
                    if la.len() != lb.len() {
                        return Err(Fail);
                    }
                    for (x, y) in la.iter().zip(&lb) {
                        match (x, y) {
                            (Operand::Expr(p), Operand::Expr(q)) => self.cmp_expr(*p, &Node::Expr(*q), i, j, false)?,
                            (Operand::Var(p), Operand::Var(q)) => self.map_var(*p, *q)?,
                            _ => {
                                if x != y {
                                    return Err(Fail);
                                }
                            }
                        }
                    }
                }
                (Operand::Int(x), Operand::Int(y)) => {
                    if is_branch {
                        self.map_target(*x as u32, *y as u32)?;
                    } else if x != y {
                        return Err(Fail);
                    }
                }
                (Operand::Var(x), Operand::Var(y)) => self.map_var(*x, *y)?,
                _ => {
                    if a != b {
                        return Err(Fail);
                    }
                }
            }
        }
        // Widths may differ only where a specialised value was substituted.
        if f.size(t) != f.size(fe) && self.replaced_count() == before {
            return Err(Fail);
        }
        Ok(())
    }

    /// Pair two branches: same condition and targets, or the condition negated
    /// with the targets swapped (compilers invert tests freely).
    fn cmp_if(&mut self, t: ExprId, fe: ExprId, i: u32, j: u32) -> MResult<()> {
        let f = self.f;
        let ct = f.sub(t, 0).ok_or(Fail)?;
        let (tt, ft) = f.if_targets(t).ok_or(Fail)?;
        let cf = f.sub(fe, 0).ok_or(Fail)?;
        let (tf, ff) = f.if_targets(fe).ok_or(Fail)?;
        let snap = self.snapshot();
        let direct = (|| -> MResult<()> {
            self.cmp_expr(ct, &Node::Expr(cf), i, j, false)?;
            self.map_target(tt, tf)?;
            self.map_target(ft, ff)
        })();
        if direct.is_ok() {
            return Ok(());
        }
        self.restore(snap);
        let negated = complement_of(f, &Node::Expr(cf)).ok_or(Fail)?;
        self.cmp_expr(ct, &negated, i, j, false)?;
        self.map_target(tt, ff)?;
        self.map_target(ft, tf)
    }

    /// Structural equality modulo the variable map, or an explained value pair.
    /// `a` is always an expression of the kept arm; `b` may be a hybrid node
    /// (a negated comparison).  Inside an address (`address`) widths do not count.
    fn cmp_expr(&mut self, a: ExprId, b: &Node, i: u32, j: u32, address: bool) -> MResult<()> {
        let f = self.f;
        let oa = f.op(a);
        let ob = b.mlil_op(f);
        if oa == Op::Var && ob == Some(Op::Var) {
            let va = f.var_of(a).ok_or(Fail)?;
            let vb = match b.args(f).first() {
                Some(Node::Var(v, _)) => *v,
                _ => return Err(Fail),
            };
            if va == vb || self.var_map.get(&va) == Some(&vb) {
                return Ok(());
            }
            if self.explain(a, b, i, j) {
                return Ok(());
            }
            return self.map_var(va, vb);
        }
        if oa.is_const_op() && ob == Some(oa) {
            let va = f.const_value(a).ok_or(Fail)? as i128;
            let vb = b.const_value(f).ok_or(Fail)?;
            if va == vb || masked(va, f.size(a)) == masked(vb, b.size(f).unwrap_or(0)) {
                return Ok(());
            }
            return Err(Fail);
        }
        if ob == Some(oa) && f.operands(a).len() == b.arg_count(f) {
            let snap = self.snapshot();
            let before = self.replaced_count();
            let args_b = b.args(f);
            let result = (|| -> MResult<()> {
                for (k, (x, y)) in f.operands(a).iter().zip(&args_b).enumerate() {
                    match (x, y) {
                        (Operand::Expr(x), y @ (Node::Expr(_) | Node::Sited(_, _) | Node::Rn(_))) => {
                            self.cmp_expr(*x, y, i, j, address || oa.is_address_operand(k))?
                        }
                        (Operand::Expr(_), _) => return Err(Fail),
                        (_, Node::Expr(_) | Node::Sited(_, _) | Node::Rn(_)) => return Err(Fail),
                        (Operand::List { .. }, y) => {
                            if !list_equal(f, *x, y) {
                                return Err(Fail);
                            }
                        }
                        (_, Node::List(_, _)) => return Err(Fail),
                        (Operand::Int(x), y) => {
                            if y.const_value(f) != Some(*x as i128) {
                                return Err(Fail);
                            }
                        }
                        (_, Node::Int(_) | Node::Const(_)) => return Err(Fail),
                        (Operand::Var(x), Node::Var(y, _)) => self.map_var(*x, *y)?,
                        _ => return Err(Fail),
                    }
                }
                let sa = Some(f.size(a)).filter(|s| *s != 0);
                let sb = b.size(f);
                if !address && sa != sb && sa.is_some() && sb.is_some() && self.replaced_count() == before {
                    return Err(Fail);
                }
                Ok(())
            })();
            match result {
                Ok(()) => return Ok(()),
                Err(Fail) => self.restore(snap),
            }
        }
        if !self.explain(a, b, i, j) {
            return Err(Fail);
        }
        Ok(())
    }

    /// Explain the kept-arm expression `a` against the removed-arm value `b`
    /// and record that `a` is to be replaced by the call's result.
    fn explain(&mut self, a: ExprId, b: &Node, i: u32, j: u32) -> bool {
        match self.explain_pair(&Node::Expr(a), b, i, j) {
            Some(call) => {
                self.replacements.entry(i).or_default().insert(a, call);
                true
            }
            None => false,
        }
    }

    /// The index of the hoisted call whose value `a` (the kept arm's, read at
    /// `i`) and `b` (the removed arm's, read at `j`) both are: some candidate
    /// pattern's true and false arm under the site's guard.  None when no
    /// pattern explains the pair.
    fn explain_pair(&mut self, a: &Node, b: &Node, i: u32, j: u32) -> Option<usize> {
        let f = self.f;
        let empty = f.instr_set();
        let no_vars = VarSet::with_capacity(f.vars.len());
        for cand in self.candidates {
            let pattern = &self.patterns[cand.pattern];
            let Some(gv) = pattern.guarded_value() else { continue }; // a statement-run pattern explains no values
            let (site_true, site_false) = if cand.swap { (&gv.false_arm, &gv.true_arm) } else { (&gv.true_arm, &gv.false_arm) };
            let (arm_k, arm_r) = if self.kept_is_true { (site_true, site_false) } else { (site_false, site_true) };
            let mut state = State::new(self.round, pattern, &empty, &no_vars, self.rules, Vec::new());
            state.set_bindings(cand.bindings.clone(), cand.bind_site.clone());
            // Whether the pattern guard holds on the kept arm: it holds on the site's
            // true arm unless the pattern matched the negated condition.
            let kept_polarity = if self.kept_is_true { !cand.swap } else { cand.swap };
            let outcome = (|| -> MResult<()> {
                state.facts = state.guard_facts(&[], &cand.guard, &cand.form, cand.form_direct, kept_polarity);
                state.use_index = i as i32;
                state.match_expr(arm_k, a)?;
                state.facts = state.guard_facts(&[], &cand.guard, &cand.form, cand.form_direct, !kept_polarity);
                state.use_index = j as i32;
                state.match_expr(arm_r, b)?;
                Ok(())
            })();
            state.use_index = -1;
            if outcome.is_err() {
                continue;
            }
            let mut chased = cand.chased.clone();
            for c in &state.chased {
                if !chased.iter().any(|(d, _)| *d == c.0) {
                    chased.push(*c);
                }
            }
            let call = HoistedCall {
                pattern: cand.pattern,
                bindings: state.bindings.clone(),
                chased,
                example: a.expr_id(),
                bind_site: state.bind_site.clone(),
                var: None,
            };
            return Some(self.dedupe(call));
        }
        None
    }

    /// A run of statements at the start of both arms that a void diamond
    /// pattern stands for as one call: its true-arm statements match the kept
    /// arm's first instructions and its false-arm statements the removed
    /// arm's (or the other way round when the pattern matched the guard
    /// negated).  Records the hoisted call and returns how many instructions
    /// each arm gives up.
    fn explain_run(&mut self, bt: BlockId, bf: BlockId) -> Option<(usize, usize)> {
        let f = self.f;
        let (ts, te) = (f.block(bt).start, f.block(bt).end);
        let (fs, fe) = (f.block(bf).start, f.block(bf).end);
        let empty = f.instr_set();
        let no_vars = VarSet::with_capacity(f.vars.len());
        for cand in self.candidates {
            let pattern = &self.patterns[cand.pattern];
            let Some(gs) = pattern.guarded_statements() else { continue };
            let (site_true, site_false) = if cand.swap { (&gs.false_arm, &gs.true_arm) } else { (&gs.true_arm, &gs.false_arm) };
            let (arm_k, arm_r) = if self.kept_is_true { (site_true, site_false) } else { (site_false, site_true) };
            if ts + arm_k.len() as u32 > te || fs + arm_r.len() as u32 > fe {
                continue;
            }
            let kept_polarity = if self.kept_is_true { !cand.swap } else { cand.swap };
            let mut state = State::new(self.round, pattern, &empty, &no_vars, self.rules, Vec::new());
            state.set_bindings(cand.bindings.clone(), cand.bind_site.clone());
            let outcome = (|| -> MResult<()> {
                state.facts = state.guard_facts(&[], &cand.guard, &cand.form, cand.form_direct, kept_polarity);
                match_run(&mut state, arm_k, ts)?;
                state.facts = state.guard_facts(&[], &cand.guard, &cand.form, cand.form_direct, !kept_polarity);
                match_run(&mut state, arm_r, fs)
            })();
            state.use_index = -1;
            if outcome.is_err() {
                continue;
            }
            // The run only leaves behind what the call re-establishes (the objects
            // passed by address); anything else it writes must be dead after it.
            let mut by_ref = VarSet::with_capacity(f.vars.len());
            for n in pattern.reference_placeholders().iter() {
                if let Some(v) = state.bindings[n.0 as usize].as_ref().and_then(|b| b.redefined_var()) {
                    by_ref.insert(v.0 as usize);
                }
            }
            for v in &state.clobbered {
                by_ref.insert(v.0 as usize); // outputs a `... = call` matched are nobody's value
            }
            let mut kept_run = f.instr_set();
            for k in ts..ts + arm_k.len() as u32 {
                kept_run.insert(k as usize);
            }
            let mut removed_run = f.instr_set();
            for k in fs..fs + arm_r.len() as u32 {
                removed_run.insert(k as usize);
            }
            if !self.run_values_die(&kept_run, &by_ref) || !self.run_values_die(&removed_run, &by_ref) {
                continue;
            }
            let mut chased = cand.chased.clone();
            for c in &state.chased {
                if !chased.iter().any(|(d, _)| *d == c.0) {
                    chased.push(*c);
                }
            }
            let call = self.dedupe(HoistedCall {
                pattern: cand.pattern,
                bindings: state.bindings.clone(),
                chased,
                example: None,
                bind_site: state.bind_site.clone(),
                var: None,
            });
            self.runs.push((ts, arm_k.len(), fs, arm_r.len(), call));
            return Some((arm_k.len(), arm_r.len()));
        }
        None
    }

    fn run_values_die(&self, run: &InstrSet, by_ref: &VarSet) -> bool {
        for idx in run.ones() {
            for var in self.f.vars_written(self.f.instr(idx as u32)) {
                if by_ref.contains(var.0 as usize) {
                    continue;
                }
                if self.round.env.uses_outside(self.f, idx as u32, run, var) {
                    return false;
                }
            }
        }
        true
    }

    fn dedupe(&mut self, call: HoistedCall) -> usize {
        let f = self.f;
        let pattern = &self.patterns[call.pattern];
        for k in 0..self.calls.len() {
            let existing = &self.calls[k];
            let same_function = existing.pattern == call.pattern
                || (!pattern.name.is_empty() && self.patterns[existing.pattern].name == pattern.name);
            if !same_function {
                continue;
            }
            let mut same = true;
            for id in pattern.param_ids() {
                let (x, y) = match id {
                    Some(id) => (existing.binding(id), call.binding(id)),
                    None => (None, None),
                };
                match (x, y) {
                    (Some(x), Some(y)) if x.kind_name() == y.kind_name() && x.same(y, f) => {}
                    _ => {
                        same = false;
                        break;
                    }
                }
            }
            if same {
                let existing = &mut self.calls[k];
                for c in &call.chased {
                    if !existing.chased.iter().any(|(d, _)| *d == c.0) {
                        existing.chased.push(*c);
                    }
                }
                return k;
            }
        }
        self.calls.push(call);
        self.calls.len() - 1
    }
}

fn list_equal(f: &Function, x: Operand, y: &Node) -> bool {
    let Node::List(start, len) = y else { return false };
    let (lx, ly) = (f.list(x), f.list(Operand::List { start: *start, len: *len }));
    lx.len() == ly.len() && lx.iter().zip(ly).all(|(p, q)| p == q)
}

fn match_run(state: &mut State, stmts: &[Stmt], start: u32) -> MResult<()> {
    for (k, stmt) in stmts.iter().enumerate() {
        state.use_index = (start + k as u32) as i32;
        state.match_stmt(stmt, state.f.instr(start + k as u32))?;
    }
    Ok(())
}

// --------------------------------------------------------------------------- driver

/// Find shared-guard fusions to unfuse.  `extra_deleted` are instructions
/// other matches already remove (their uses no longer count); `extra_live`
/// are variables other matches pass as call arguments (their definitions must
/// stay).
pub fn find_fused_matches(
    round: &Round,
    patterns: &[Pattern],
    rules: &[Rule],
    exclude_blocks: Option<&BlockSet>,
    extra_deleted: &InstrSet,
    extra_live: &VarSet,
) -> Vec<FusedMatch> {
    let f = round.f;
    let pure: Vec<usize> = patterns
        .iter()
        .enumerate()
        .filter(|(_, p)| (p.pure && p.guarded_value().is_some() && p.returns) || p.guarded_statements().is_some())
        .map(|(i, _)| i)
        .collect();
    if pure.is_empty() {
        return Vec::new();
    }
    let mut gone = f.instr_set();
    gone.union_with(extra_deleted);
    let mut live = VarSet::with_capacity(f.vars.len());
    live.union_with(extra_live);
    let doms = compute_dominators(f);
    let mut taken = f.block_set();
    if let Some(x) = exclude_blocks {
        taken.union_with(x);
    }
    let mut results: Vec<FusedMatch> = Vec::new();

    for block in &f.blocks {
        if taken.contains(block.id.0 as usize) || block.end == block.start {
            continue;
        }
        let guard = f.instr(block.end - 1);
        if f.op(guard) != Op::If {
            continue;
        }
        let Some(cond) = f.sub(guard, 0) else { continue };
        let Some((t, fl)) = f.if_targets(guard) else { continue };
        if t == fl || t as usize >= f.len() || fl as usize >= f.len() {
            continue;
        }
        let (Some(tb), Some(fb)) = (f.block_at(t), f.block_at(fl)) else { continue };
        let mut st = f.block_set();
        let mut sf = f.block_set();
        for b in &f.blocks {
            if doms[b.id.0 as usize].contains(tb.id.0 as usize) {
                st.insert(b.id.0 as usize);
            }
            if doms[b.id.0 as usize].contains(fb.id.0 as usize) {
                sf.insert(b.id.0 as usize);
            }
        }
        let overlap = !st.is_disjoint(&sf);
        let mut union = st.clone();
        union.union_with(&sf);
        if overlap || st.contains(block.id.0 as usize) || sf.contains(block.id.0 as usize) || !union.is_disjoint(&taken) {
            continue;
        }
        let candidates = guard_candidates(round, patterns, &pure, block.end - 1, cond, rules);
        if candidates.is_empty() {
            continue;
        }
        let mut found: Option<FusedMatch> = None;
        for (kept_start, removed_start, kept_set, removed_set, kept_is_true) in
            [(tb.id, fb.id, &st, &sf, true), (fb.id, tb.id, &sf, &st, false)]
        {
            let mut iso = Iso::new(round, patterns, &candidates, rules, kept_set, removed_set, kept_is_true);
            if iso.run(kept_start, removed_start).is_err() {
                continue;
            }
            if iso.calls.is_empty() && iso.extras_k.is_empty() {
                continue; // plain duplication: nothing a pattern explains (extras may still yield a call)
            }
            let fm = finish(round, patterns, block.id, block.end - 1, kept_start, removed_start, kept_set, removed_set, &mut iso, &candidates, &gone, &live, kept_is_true, &doms);
            if let Some(fm) = fm {
                if !fm.calls.is_empty() {
                    found = Some(fm);
                    break;
                }
            }
        }
        let Some(fm) = found else { continue };
        for start in &fm.blocks_touched {
            if let Some(b) = f.block_at(*start) {
                taken.insert(b.id.0 as usize);
            }
        }
        gone.union_with(&fm.deleted);
        for call in &fm.calls {
            let pattern = &patterns[call.pattern];
            for id in pattern.param_ids().into_iter().flatten() {
                if let Some(b) = call.binding(id) {
                    for v in b.reads(f) {
                        live.insert(v.0 as usize);
                    }
                }
            }
        }
        results.push(fm);
    }
    results
}

fn starts(f: &Function, set: &BlockSet) -> Vec<u32> {
    let mut out: Vec<u32> = set.ones().map(|b| f.block(BlockId(b as u32)).start).collect();
    out.sort_unstable();
    out
}

#[allow(clippy::too_many_arguments)]
fn finish(
    round: &Round,
    patterns: &[Pattern],
    guard_block: BlockId,
    guard_index: u32,
    kept_start: BlockId,
    removed_start: BlockId,
    kept: &BlockSet,
    removed: &BlockSet,
    iso: &mut Iso,
    candidates: &[Candidate],
    gone: &InstrSet,
    live: &VarSet,
    kept_is_true: bool,
    doms: &[BlockSet],
) -> Option<FusedMatch> {
    let f = round.f;
    let env = round.env;
    let mut deleted = f.instr_set();
    deleted.insert(guard_index as usize);
    for s in removed.ones() {
        for i in f.block(BlockId(s as u32)).range() {
            deleted.insert(i as usize);
        }
    }
    for (start, count, _, _, _) in &iso.runs {
        for i in *start..*start + *count as u32 {
            deleted.insert(i as usize); // the kept arm's part of an explained run
        }
    }

    // Definitions that only fed the explained values (or the guard) can go.  A
    // use reached through a merge with a kept-arm definition does not count:
    // once the removed arm is gone only the kept definition arrives there.
    fn settle(f: &Function, env: &dyn crate::env::Env, iso: &Iso, candidates: &[Candidate], deleted: &mut InstrSet, gone: &InstrSet, live: &VarSet, kept: &BlockSet) {
        // Which variable occurrences vanish because their expression is replaced by a call result.
        let mut reads_by: HashMap<u32, Vec<VarId>> = HashMap::new();
        for (i, repl) in &iso.replacements {
            let mut reads = Vec::new();
            for e in repl.keys() {
                reads.extend(f.vars_read(*e));
            }
            reads_by.insert(*i, reads);
        }
        let fully_replaced = |i: u32, var: VarId| -> bool {
            let total = f.vars_read(f.instr(i)).iter().filter(|v| **v == var).count();
            let vanished = reads_by.get(&i).map(|r| r.iter().filter(|v| **v == var).count()).unwrap_or(0);
            total > 0 && total == vanished
        };
        let mut candidates_del: BTreeMap<u32, VarId> = BTreeMap::new();
        for call in &iso.calls {
            for (d, v) in &call.chased {
                candidates_del.insert(*d, *v);
            }
        }
        for cand in candidates {
            for (d, v) in &cand.chased {
                candidates_del.insert(*d, *v);
            }
        }
        for i in iso.extras_k.keys() {
            if let Some(v) = f.var_operand(f.instr(*i), 0) {
                candidates_del.insert(*i, v);
            }
        }
        let mut changed = true;
        while changed {
            changed = false;
            for (d, var) in &candidates_del {
                let (d, var) = (*d, *var);
                if deleted.contains(d as usize) || gone.contains(d as usize) || live.contains(var.0 as usize) || iso.replacements.contains_key(&d) {
                    continue;
                }
                let uses = env.uses_of(f, d, var, Some(kept));
                if uses.iter().all(|u| deleted.contains(*u as usize) || gone.contains(*u as usize) || fully_replaced(*u, var)) {
                    deleted.insert(d as usize);
                    changed = true;
                }
            }
        }
    }

    settle(f, env, iso, candidates, &mut deleted, gone, live, kept);
    // A kept-arm reassignment with no counterpart whose value is still needed
    // (it reaches the join) is paired with the removed arm's implicit identity:
    // `v = <kept-arm value>` against `v` as the removed arm leaves it.  Explained
    // by a pattern, the reassignment is dropped and the call result substituted
    // into every read it reaches, so `v` keeps its original value (later
    // patterns may still need it as an argument).  Where a read might also see
    // some other value the assignment form `v = <call result>` stays.
    let guard_block_start = f.block(guard_block).start;
    let extras_k: Vec<(u32, u32)> = iso.extras_k.iter().map(|(i, j)| (*i, *j)).collect();
    for (i, j) in extras_k {
        if deleted.contains(i as usize) {
            continue;
        }
        let instr = f.instr(i);
        if f.op(instr) != Op::SetVar {
            return None;
        }
        let dest = f.var_operand(instr, 0)?;
        let src = f.sub(instr, 1)?;
        let snap = iso.snapshot();
        if !iso.explain(src, &Node::Var(dest, j as i32), i, j) {
            iso.restore(snap);
            return None;
        }
        let substitutions = substitution_sites(round, iso, i, dest, guard_index, guard_block, doms, kept, removed, &deleted, &InstrSet::with_capacity(0));
        if let Some(substitutions) = substitutions {
            let call_index = iso.replacements[&i][&src];
            iso.replacements.remove(&i);
            deleted.insert(i as usize);
            for (u, exprs) in substitutions {
                for e in exprs {
                    iso.replacements.entry(u).or_default().insert(e, call_index);
                }
            }
        }
    }
    settle(f, env, iso, candidates, &mut deleted, gone, live, kept);
    for i in iso.extras_k.keys() {
        if !deleted.contains(*i as usize) && !iso.replacements.contains_key(i) {
            return None;
        }
    }

    // A removed-arm assignment with no counterpart whose value reaches the join
    // is that arm's version of a value the kept arm leaves as it found it (the
    // short arm loading the size into the register the long arm already holds
    // it in).  Explained by a pattern (the kept arm's value as its true arm, the
    // assignment as its false arm) the call result takes its place: substituted
    // into the reads it reaches when the only other value arriving there is the
    // explained kept one, else assigned to the variable after the hoisted calls.
    // Unexplained, the fusion would change what the code after the join sees.
    let mut removed_region = f.instr_set();
    for s in removed.ones() {
        for i in f.block(BlockId(s as u32)).range() {
            removed_region.insert(i as usize);
        }
    }
    let kept_last = f.block(kept_start).end - 1;
    let mut assignments: Vec<(VarId, usize)> = Vec::new();
    let extras_r: Vec<u32> = iso.extras_r.iter().copied().collect();
    for j in extras_r {
        let instr = f.instr(j);
        if f.op(instr) != Op::SetVar {
            return None;
        }
        let dest = f.var_operand(instr, 0)?;
        let src = f.sub(instr, 1)?;
        let uses = env.uses_of(f, j, dest, Some(kept));
        if uses.iter().all(|u| removed_region.contains(*u as usize) || deleted.contains(*u as usize) || gone.contains(*u as usize)) {
            continue;
        }
        let call_index = iso.explain_pair(&Node::Var(dest, kept_last as i32), &Node::Expr(src), kept_last, j)?;
        let mut identity = f.instr_set();
        for (d, _) in &iso.calls[call_index].chased {
            identity.insert(*d as usize);
        }
        let substitutions = substitution_sites(round, iso, j, dest, guard_index, guard_block, doms, kept, removed, &deleted, &identity);
        match substitutions {
            None => assignments.push((dest, call_index)),
            Some(substitutions) => {
                for (u, exprs) in substitutions {
                    for e in exprs {
                        iso.replacements.entry(u).or_default().insert(e, call_index);
                    }
                }
            }
        }
    }
    settle(f, env, iso, candidates, &mut deleted, gone, live, kept);

    // Arguments are evaluated at the guard: between where an argument was
    // observed and the guard, nothing that survives may overwrite what it reads.
    let mut all_skip = deleted.clone();
    all_skip.union_with(gone);
    for call in &iso.calls {
        let pattern = &patterns[call.pattern];
        for id in pattern.param_ids() {
            let id = id?;
            let b = call.binding(id)?;
            let site = call.bind_site[id.0 as usize];
            if site < 0 {
                continue;
            }
            if writes_between(f, site as u32, guard_index, &b.reads(f), &all_skip) {
                return None;
            }
        }
    }

    let mut touched = kept.clone();
    touched.union_with(removed);
    touched.insert(guard_block.0 as usize);
    Some(FusedMatch {
        guard_index,
        guard_block: guard_block_start,
        kept_block: f.block(kept_start).start,
        removed_block: f.block(removed_start).start,
        kept_blocks: starts(f, kept),
        removed_blocks: starts(f, removed),
        deleted,
        calls: iso.calls.clone(),
        replacements: iso.replacements.clone(),
        blocks_touched: starts(f, &touched),
        kept_is_true,
        assignments,
    })
}

/// Where the reads of the reassignment at `i` can take the call result
/// instead: {instruction: [expressions]}.  None when some read might also see
/// another value: a merge outside the guard's reach, one fed by a value from
/// elsewhere (other than a definition in `identity_defs`, the explained value
/// the other arm left untouched), or a read through a field or address.
#[allow(clippy::too_many_arguments)]
fn substitution_sites(
    round: &Round,
    iso: &Iso,
    i: u32,
    dest: VarId,
    guard_index: u32,
    guard_block: BlockId,
    doms: &[BlockSet],
    kept: &BlockSet,
    removed: &BlockSet,
    deleted: &InstrSet,
    identity_defs: &InstrSet,
) -> Option<BTreeMap<u32, Vec<ExprId>>> {
    let f = round.f;
    let env = round.env;
    let merges = env.merges_of(f, i, dest, guard_index)?;
    let mut arm_writes = false;
    for b in kept.ones().chain(removed.ones()) {
        for k in f.block(BlockId(b as u32)).range() {
            if k != i && f.vars_written(f.instr(k)).contains(&dest) {
                arm_writes = true;
            }
        }
    }
    for m in merges {
        let mb = f.block_id_of(m.block_start);
        if !doms[mb.0 as usize].contains(guard_block.0 as usize) {
            return None; // a path from elsewhere joins here
        }
        for d in m.others {
            match d {
                crate::env::MergeSource::Unknown => return None,
                crate::env::MergeSource::Live => {
                    if arm_writes {
                        return None; // the untouched value only means "as the removed arm leaves it" if nothing else wrote it
                    }
                }
                crate::env::MergeSource::Def(d) => {
                    if !removed.contains(f.block_id_of(d).0 as usize) && !deleted.contains(d as usize) && !identity_defs.contains(d as usize) {
                        return None;
                    }
                }
            }
        }
    }
    let _ = iso;
    let mut out: BTreeMap<u32, Vec<ExprId>> = BTreeMap::new();
    for u in env.uses_of(f, i, dest, None) {
        if deleted.contains(u as usize) {
            continue;
        }
        let instr = f.instr(u);
        let mut subs = Vec::new();
        f.subexprs(instr, &mut subs);
        let nodes: Vec<ExprId> = subs.into_iter().filter(|n| f.op(*n) == Op::Var && f.var_of(*n) == Some(dest)).collect();
        if nodes.len() != f.vars_read(instr).iter().filter(|v| **v == dest).count() {
            return None;
        }
        out.insert(u, nodes);
    }
    Some(out)
}
