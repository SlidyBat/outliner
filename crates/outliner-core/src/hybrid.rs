//! Hybrid trees: the code's own expressions mixed with forms produced by
//! instantiating a rewrite rule's right side or a pattern guard.
//!
//! A [`Node`] is what the matcher matches pattern expressions against.  Code
//! expressions are referenced by id, rewritten forms are small reference-counted
//! trees, and both may carry the instruction they were read at so that
//! definition lookups for the variables inside them start from the right place.

use std::rc::Rc;

use crate::binding::{Binding, MemberBase, MemberKind};
use crate::il::{ExprId, Function, Operand, VarId};
use crate::ops::Op;
use crate::pattern::{CallExpr, Expr, PhId, SymbolRef};

/// The operation of a rewritten node: an MLIL operation, or a call result
/// inside a guard (only ever compared with other instantiated pattern text).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum HOp {
    Op(Op),
    /// `call(name, ...)` with a symbol target, or any target when None.
    Call(Option<Rc<str>>),
}

impl HOp {
    pub fn op(&self) -> Option<Op> {
        match self {
            HOp::Op(op) => Some(*op),
            HOp::Call(_) => None,
        }
    }
}

/// An operation produced by instantiating a rule's right side (or a pattern
/// guard): operation, size (None = unspecified) and hybrid children.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct RNode {
    pub op: HOp,
    pub size: Option<u16>,
    pub args: Vec<Node>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Node {
    /// A code expression.
    Expr(ExprId),
    /// A code expression together with the instruction it belongs to: definition
    /// lookups for variables inside it start there, not where the matcher is.
    Sited(ExprId, u32),
    /// A variable in an expression position, with the instruction it was read at (-1: unknown).
    Var(VarId, i32),
    Rn(Rc<RNode>),
    /// A pattern constant.
    Const(i128),
    /// A raw integer operand of the code.
    Int(i64),
    Float(u64),
    /// A raw list operand of the code (start, len).
    List(u32, u32),
    Symbol(Rc<SymbolRef>),
    Wildcard,
    /// An operand nothing but a wildcard matches.
    Other,
}

impl Node {
    pub fn rn(op: Op, size: Option<u16>, args: Vec<Node>) -> Node {
        Node::Rn(Rc::new(RNode { op: HOp::Op(op), size, args }))
    }

    pub fn from_operand(o: Operand) -> Node {
        match o {
            Operand::Expr(e) => Node::Expr(e),
            Operand::Var(v) => Node::Var(v, -1),
            Operand::Int(i) => Node::Int(i),
            Operand::Float(bits) => Node::Float(bits),
            Operand::List { start, len } => Node::List(start, len),
            _ => Node::Other,
        }
    }

    /// Without the site.
    pub fn unsited(&self) -> Node {
        match self {
            Node::Sited(e, _) => Node::Expr(*e),
            other => other.clone(),
        }
    }

    pub fn expr_id(&self) -> Option<ExprId> {
        match self {
            Node::Expr(e) | Node::Sited(e, _) => Some(*e),
            _ => None,
        }
    }

    pub fn is_code(&self) -> bool {
        matches!(self, Node::Expr(_) | Node::Sited(_, _))
    }

    pub fn is_var(&self) -> bool {
        matches!(self, Node::Var(_, _))
    }

    pub fn is_rn(&self) -> bool {
        matches!(self, Node::Rn(_))
    }

    /// The operation of a code expression or rewritten node.
    pub fn op(&self, f: &Function) -> Option<HOp> {
        match self {
            Node::Expr(e) | Node::Sited(e, _) => Some(HOp::Op(f.op(*e))),
            Node::Rn(r) => Some(r.op.clone()),
            _ => None,
        }
    }

    pub fn mlil_op(&self, f: &Function) -> Option<Op> {
        match self {
            Node::Expr(e) | Node::Sited(e, _) => Some(f.op(*e)),
            Node::Rn(r) => r.op.op(),
            _ => None,
        }
    }

    /// The size of a code expression (None when zero) or rewritten node.
    pub fn size(&self, f: &Function) -> Option<u16> {
        match self {
            Node::Expr(e) | Node::Sited(e, _) => Some(f.size(*e)).filter(|s| *s != 0),
            Node::Rn(r) => r.size,
            _ => None,
        }
    }

    /// The operands of a code expression or rewritten node, as nodes.
    pub fn args(&self, f: &Function) -> Vec<Node> {
        match self {
            Node::Expr(e) | Node::Sited(e, _) => f.operands(*e).iter().map(|o| Node::from_operand(*o)).collect(),
            Node::Rn(r) => r.args.clone(),
            _ => Vec::new(),
        }
    }

    pub fn arg_count(&self, f: &Function) -> usize {
        match self {
            Node::Expr(e) | Node::Sited(e, _) => f.operands(*e).len(),
            Node::Rn(r) => r.args.len(),
            _ => 0,
        }
    }

    /// The value of a constant: a pattern constant, a raw integer, or a constant expression.
    pub fn const_value(&self, f: &Function) -> Option<i128> {
        match self {
            Node::Const(c) => Some(*c),
            Node::Int(i) => Some(*i as i128),
            Node::Expr(e) | Node::Sited(e, _) => f.const_value(*e).map(|v| v as i128),
            _ => None,
        }
    }

    /// The variable a leaf denotes, or None.
    pub fn leaf_var(&self, f: &Function) -> Option<VarId> {
        match self {
            Node::Var(v, _) => Some(*v),
            Node::Expr(e) | Node::Sited(e, _) => f.var_of(*e),
            _ => None,
        }
    }
}

/// Matching failed; every binding is rolled back by the caller.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Fail;

pub type MResult<T> = Result<T, Fail>;

/// Substitute bound placeholders into a pattern expression, giving a hybrid
/// tree whose leaves are code expressions, variables or constants.  `sites`
/// holds, per placeholder, the instruction its binding was established at.
pub fn instantiate(expr: &Expr, bindings: &[Option<Binding>], sites: &[i32]) -> MResult<Node> {
    match expr {
        Expr::Placeholder(p) => {
            let b = bindings.get(p.0 as usize).and_then(|b| b.as_ref()).ok_or(Fail)?;
            let site = sites.get(p.0 as usize).copied().unwrap_or(-1);
            Ok(match b {
                Binding::Expr { expr, .. } => {
                    if site >= 0 {
                        Node::Sited(*expr, site as u32)
                    } else {
                        Node::Expr(*expr)
                    }
                }
                Binding::Var(v) => Node::Var(*v, site),
                Binding::Addr(v) => Node::rn(Op::AddressOf, None, vec![Node::Var(*v, site)]),
                Binding::Member(m) => {
                    let base = match (m.kind, m.base) {
                        (MemberKind::Var, MemberBase::Var(v)) => {
                            return Ok(Node::rn(Op::AddressOfField, None, vec![Node::Var(v, site), Node::Const(m.offset as i128)]));
                        }
                        (MemberKind::Ptr, MemberBase::Var(v)) => Node::Var(v, site),
                        (MemberKind::Addr, MemberBase::Var(v)) => Node::rn(Op::AddressOf, None, vec![Node::Var(v, site)]),
                        (_, MemberBase::Expr(e)) => {
                            if site >= 0 {
                                Node::Sited(e, site as u32)
                            } else {
                                Node::Expr(e)
                            }
                        }
                        (_, MemberBase::Var(v)) => Node::Var(v, site),
                    };
                    Node::rn(Op::Add, None, vec![base, Node::Const(m.offset as i128)])
                }
                Binding::Int { value, .. } => Node::Const(*value),
                Binding::Bytes { bytes, .. } => Node::Const(crate::binding::bytes_to_i128(bytes).ok_or(Fail)?),
                // a pointer to a global is its address; the object itself has no value to stand in
                Binding::Global { addr, object: false } => Node::Const(*addr as i128),
                Binding::Global { object: true, .. } => return Err(Fail),
            })
        }
        Expr::Wildcard => Ok(Node::Wildcard),
        Expr::Const(c) => Ok(Node::Const(*c)),
        Expr::Symbol(s) => Ok(Node::Symbol(Rc::new(s.clone()))),
        Expr::Op(o) => {
            // A field of a global: the code spells it as a plain load or store at the
            // constant address (`[&g + 0x17].b`), so the tree is built that way to
            // compare equal to the code (branch facts, `when` conditions).
            if let (Some(flat), Some(Expr::Placeholder(p)), Some(Expr::Const(off))) = (o.op.flat_field_op(), o.args.first(), o.args.get(1)) {
                if let Some(Binding::Global { addr, .. }) = bindings.get(p.0 as usize).and_then(|b| b.as_ref()) {
                    let mut args = vec![Node::Const(*addr as i128 + *off)];
                    for a in &o.args[2..] {
                        args.push(instantiate(a, bindings, sites)?);
                    }
                    return Ok(Node::rn(flat, o.size, args));
                }
            }
            let args = o.args.iter().map(|a| instantiate(a, bindings, sites)).collect::<MResult<Vec<_>>>()?;
            Ok(Node::rn(o.op, o.size, args))
        }
        Expr::Call(c) => instantiate_call(c, bindings, sites),
    }
}

fn instantiate_call(c: &CallExpr, bindings: &[Option<Binding>], sites: &[i32]) -> MResult<Node> {
    let mut args: Vec<Node> = Vec::with_capacity(c.args.len() + 1);
    let op = match &c.target {
        Expr::Symbol(s) => HOp::Call(Some(Rc::from(s.name.as_str()))),
        other => {
            args.push(instantiate(other, bindings, sites)?);
            HOp::Call(None)
        }
    };
    for a in &c.args {
        args.push(instantiate(a, bindings, sites)?);
    }
    Ok(Node::Rn(Rc::new(RNode { op, size: None, args })))
}

/// Whether two placeholders' worth of expressions instantiate to equal trees.
pub fn placeholders_of(expr: &Expr) -> Vec<PhId> {
    let mut set = crate::pattern::PhSet::default();
    crate::pattern::collect_placeholders(expr, &mut set);
    set.iter().collect()
}

/// Two variable reads may denote the same value (one is a copy of the other).
pub type LeafEq<'a> = &'a dyn Fn(VarId, i32, VarId, i32) -> bool;

/// Equality of hybrid trees (code expressions, rewritten nodes, constants).
/// `leaf_eq` may declare two variables the same value; `ctx` is the instruction
/// a leaf was read at, updated when a sited leaf is entered.
pub fn hybrid_equal(f: &Function, a: &Node, b: &Node, leaf_eq: Option<LeafEq>, ctx_a: i32, ctx_b: i32) -> bool {
    let (mut ctx_a, mut ctx_b) = (ctx_a, ctx_b);
    let a = match a {
        Node::Sited(e, u) => {
            ctx_a = *u as i32;
            Node::Expr(*e)
        }
        Node::Var(_, u) if *u >= 0 => {
            ctx_a = *u;
            a.clone()
        }
        other => other.clone(),
    };
    let b = match b {
        Node::Sited(e, u) => {
            ctx_b = *u as i32;
            Node::Expr(*e)
        }
        Node::Var(_, u) if *u >= 0 => {
            ctx_b = *u;
            b.clone()
        }
        other => other.clone(),
    };
    if matches!(a, Node::Wildcard) || matches!(b, Node::Wildcard) {
        return true;
    }
    let (va, vb) = (a.const_value(f), b.const_value(f));
    if va.is_some() || vb.is_some() {
        // the other side may be a sum the decompiler left unfolded (`&g + 0x17`)
        let (Some(va), Some(vb)) = (va.or_else(|| folded_const(f, &a)), vb.or_else(|| folded_const(f, &b))) else { return false };
        let size = a.size(f).or_else(|| b.size(f)).unwrap_or(0);
        return const_equal(va, vb, size);
    }
    let (xa, xb) = (a.leaf_var(f), b.leaf_var(f));
    if xa.is_some() || xb.is_some() {
        let (Some(xa), Some(xb)) = (xa, xb) else { return false };
        if xa == xb {
            return true;
        }
        return leaf_eq.map(|eq| eq(xa, ctx_a, xb, ctx_b)).unwrap_or(false);
    }
    if let (Node::List(sa, la), Node::List(sb, lb)) = (&a, &b) {
        let (la, lb) = (f.list(Operand::List { start: *sa, len: *la }), f.list(Operand::List { start: *sb, len: *lb }));
        return la.len() == lb.len()
            && la
                .iter()
                .zip(lb)
                .all(|(x, y)| hybrid_equal(f, &Node::from_operand(*x), &Node::from_operand(*y), leaf_eq, ctx_a, ctx_b));
    }
    match (a.op(f), b.op(f)) {
        (Some(oa), Some(ob)) if oa == ob => {}
        _ => return false,
    }
    if let (Some(sa), Some(sb)) = (a.size(f), b.size(f)) {
        if sa != sb {
            return false;
        }
    }
    let (args_a, args_b) = (a.args(f), b.args(f));
    args_a.len() == args_b.len()
        && args_a.iter().zip(&args_b).all(|(x, y)| hybrid_equal(f, x, y, leaf_eq, ctx_a, ctx_b))
}

/// The value of a constant, or of a sum or difference of constants (an
/// address the decompiler left as `&g + 0x17`).
pub fn folded_const(f: &Function, node: &Node) -> Option<i128> {
    if let Some(v) = node.const_value(f) {
        return Some(v);
    }
    let args = node.args(f);
    match node.mlil_op(f)? {
        Op::Add if args.len() == 2 => Some(folded_const(f, &args[0])?.wrapping_add(folded_const(f, &args[1])?)),
        Op::Sub if args.len() == 2 => Some(folded_const(f, &args[0])?.wrapping_sub(folded_const(f, &args[1])?)),
        _ => None,
    }
}

/// Two constants agree, modulo the width they are compared at.
pub fn const_equal(actual: i128, wanted: i128, size: u16) -> bool {
    if actual == wanted {
        return true;
    }
    if size > 0 && size <= 16 {
        let bits = 8 * size as u32;
        if bits >= 128 {
            return actual == wanted;
        }
        let mask = (1i128 << bits) - 1;
        return (actual.wrapping_sub(wanted)) & mask == 0;
    }
    false
}

/// The branch condition `cond` negated, as a hybrid node with the complementary
/// comparison, or None when it is not a comparison.
pub fn complement_of(f: &Function, cond: &Node) -> Option<Node> {
    let op = cond.mlil_op(f)?.complement()?;
    Some(Node::rn(op, cond.size(f), cond.args(f)))
}

/// Express a condition with a canonical comparison operator, flipping the polarity as needed.
pub fn normalize_condition(f: &Function, cond: &Node, polarity: bool) -> (Node, bool) {
    if let Some(canonical) = cond.mlil_op(f).and_then(|op| op.canonical_cmp()) {
        return (Node::rn(canonical, cond.size(f), cond.args(f)), !polarity);
    }
    (cond.clone(), polarity)
}
