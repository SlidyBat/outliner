//! Expression sites: occurrences of `value:` patterns inside instructions.
//!
//! Not every inlined call gets a variable of its own.  A `value:` pattern
//! outlines an expression wherever it occurs inside an instruction; each site
//! becomes `t = f(args)` immediately before the instruction with `t`
//! substituted for the expression, or, when the expression is the whole
//! right-hand side of an assignment, the assigned variable receives the
//! result directly.

use std::collections::HashMap;

use crate::binding::Binding;
use crate::hybrid::Node;
use crate::il::{BlockSet, ExprId, Function, InstrSet, VarId};
use crate::matcher::{value_ops, writes_between, OpSet, Round, State, VarSet};
use crate::ops::Op;
use crate::pattern::{Pattern, Rule};

#[derive(Clone, Debug)]
pub struct ExprSite {
    pub pattern: usize,
    pub instr_index: u32,
    pub expr: ExprId,
    pub bindings: Vec<Option<Binding>>,
    pub chased: Vec<(u32, VarId)>,
    /// Definitions that only fed this site.
    pub deleted: InstrSet,
    /// The site is the entire right-hand side of a set_var.
    pub whole_rhs: bool,
    /// That set_var's variable when `whole_rhs`.
    pub dest: Option<VarId>,
    pub size: u16,
    /// Fresh variable, assigned by the planner (None when the site writes `dest`).
    pub var: Option<VarId>,
}

impl ExprSite {
    pub fn entry_index(&self) -> u32 {
        self.instr_index
    }

    pub fn binding(&self, id: crate::pattern::PhId) -> Option<&Binding> {
        self.bindings.get(id.0 as usize).and_then(|b| b.as_ref())
    }

    pub fn deleted_sorted(&self) -> Vec<u32> {
        self.deleted.ones().map(|i| i as u32).collect()
    }
}

/// The variables a site's arguments read.
pub fn site_arg_vars(site: &ExprSite, pattern: &Pattern, f: &Function) -> Vec<VarId> {
    let mut out = Vec::new();
    for id in pattern.param_ids().into_iter().flatten() {
        if let Some(b) = site.binding(id) {
            for v in b.reads(f) {
                if !out.contains(&v) {
                    out.push(v);
                }
            }
        }
    }
    out
}

fn count(vars: &[VarId], v: VarId) -> usize {
    vars.iter().filter(|x| **x == v).count()
}

/// Find occurrences of `value:` patterns anywhere inside instructions.  The
/// largest occurrence wins and occurrences never nest.
pub fn find_expression_sites(
    round: &Round,
    patterns: &[Pattern],
    rules: &[Rule],
    exclude_blocks: Option<&BlockSet>,
    extra_deleted: &InstrSet,
    extra_live: &VarSet,
) -> Vec<ExprSite> {
    let f = round.f;
    let values: Vec<(usize, Option<OpSet>)> = patterns
        .iter()
        .enumerate()
        .filter(|(_, p)| p.value.is_some() && p.returns && p.pure)
        .map(|(i, p)| (i, value_ops(p, rules)))
        .collect();
    if values.is_empty() {
        return Vec::new();
    }
    let mut gone = f.instr_set();
    gone.union_with(extra_deleted);
    let mut live = VarSet::with_capacity(f.vars.len());
    live.union_with(extra_live);
    let mut hosts = f.instr_set(); // instructions already rewritten this round
    let mut consumed: HashMap<u32, Vec<VarId>> = HashMap::new(); // instruction -> variables whose reads earlier sites removed
    let mut sites: Vec<ExprSite> = Vec::new();
    let mut covered: Vec<ExprId> = Vec::new();
    for block in &f.blocks {
        if exclude_blocks.map(|x| x.contains(block.id.0 as usize)).unwrap_or(false) {
            continue;
        }
        for i in block.range() {
            if gone.contains(i as usize) {
                continue;
            }
            let instr = f.instr(i);
            if f.op(instr).no_site() {
                continue;
            }
            covered.clear();
            let rhs = if f.op(instr) == Op::SetVar { f.sub(instr, 1) } else { None };
            let mut nodes = Vec::new();
            f.subexprs(instr, &mut nodes);
            for node in nodes {
                if covered.contains(&node) {
                    continue;
                }
                let node_op = f.op(node);
                if node_op.is_const_op() {
                    continue;
                }
                for (pi, allowed) in &values {
                    if let Some(allowed) = allowed {
                        if !allowed.contains(node_op) {
                            continue;
                        }
                    }
                    let pattern = &patterns[*pi];
                    let mut state = State::new(round, pattern, &gone, &live, rules, Vec::new());
                    state.blocked_defs = Some(&hosts);
                    state.use_index = i as i32;
                    let matched = state.match_expr(pattern.value.as_ref().unwrap(), &Node::Expr(node)).is_ok();
                    state.use_index = -1;
                    if !matched {
                        continue;
                    }
                    let finished = finish_site(round, *pi, pattern, &state, i, node, rhs == Some(node), &gone, &live, &consumed);
                    drop(state);
                    let Some(site) = finished else { continue };
                    covered.extend(f.subtree(node));
                    gone.union_with(&site.deleted);
                    for v in site_arg_vars(&site, pattern, f) {
                        live.insert(v.0 as usize);
                    }
                    hosts.insert(i as usize);
                    let instr_reads = f.vars_read(instr);
                    let node_reads = f.vars_read(node);
                    let mut seen: Vec<VarId> = Vec::new();
                    for var in node_reads.iter() {
                        if seen.contains(var) {
                            continue;
                        }
                        seen.push(*var);
                        if count(&instr_reads, *var) == count(&node_reads, *var) {
                            consumed.entry(i).or_default().push(*var);
                        }
                    }
                    sites.push(site);
                    break;
                }
            }
        }
    }
    sites
}

#[allow(clippy::too_many_arguments)]
fn finish_site(
    round: &Round,
    pattern_index: usize,
    pattern: &Pattern,
    state: &State,
    i: u32,
    node: ExprId,
    whole_rhs: bool,
    gone: &InstrSet,
    live: &VarSet,
    consumed: &HashMap<u32, Vec<VarId>>,
) -> Option<ExprSite> {
    let f = round.f;
    let env = round.env;
    let instr = f.instr(i);
    // Definitions we looked through may go once nothing else needs them.
    let mut deleted = f.instr_set();
    let node_reads = f.vars_read(node);
    let instr_reads = f.vars_read(instr);
    let fully_replaced = |var: VarId| -> bool {
        let n = count(&instr_reads, var);
        n == count(&node_reads, var) && n > 0
    };
    let mut changed = true;
    while changed {
        changed = false;
        for (d, var) in &state.chased {
            let (d, var) = (*d, *var);
            if deleted.contains(d as usize) || gone.contains(d as usize) || live.contains(var.0 as usize) {
                continue;
            }
            if f.instr_op(d) == Op::Call && !env.is_pure_call(f, d) {
                continue;
            }
            let uses = env.uses_of(f, d, var, None);
            let all_fed = uses.iter().all(|u| {
                deleted.contains(*u as usize)
                    || gone.contains(*u as usize)
                    || (*u == i && fully_replaced(var))
                    || consumed.get(u).map(|c| c.contains(&var)).unwrap_or(false)
            });
            if all_fed {
                deleted.insert(d as usize);
                changed = true;
            }
        }
    }
    // The site must consume the calls it looked through: a call whose result is
    // also used elsewhere was made once in the binary, and outlining a value that
    // makes it again would show one call as two.
    if state.chased.iter().any(|(d, _)| f.instr_op(*d) == Op::Call && !deleted.contains(*d as usize)) {
        return None;
    }
    // Arguments are read when the call is emitted, just before the instruction.
    let mut all_skip = deleted.clone();
    all_skip.union_with(gone);
    for id in pattern.param_ids() {
        let id = id?;
        let b = state.bindings[id.0 as usize].as_ref()?;
        let site_index = state.bind_site[id.0 as usize];
        if site_index >= 0 && writes_between(f, site_index as u32, i, &b.reads(f), &all_skip) {
            return None;
        }
    }
    let dest = if whole_rhs { f.var_operand(instr, 0) } else { None };
    Some(ExprSite {
        pattern: pattern_index,
        instr_index: i,
        expr: node,
        bindings: state.bindings.clone(),
        chased: state.chased.clone(),
        deleted,
        whole_rhs,
        dest,
        size: if whole_rhs { f.size(instr) } else { f.size(node) },
        var: None,
    })
}
