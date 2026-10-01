//! Generalising a pattern from a second instance of the same code: the two
//! are aligned statement by statement, constants that differ become
//! placeholders, and a shape that differs becomes a chunk of its own.

use std::collections::BTreeMap;

use crate::pattern::{chunk_title, format_pattern, Block, CallExpr, Dest, Expr, IntrinsicStmt, OpNode, Pattern, PhId, Stmt, SymbolRef, RET};

/// What generalising produced.
#[derive(Clone, Debug)]
pub enum Generalized {
    /// One pattern covers both instances: the merged text and what was generalised.
    Merged { text: String, notes: Vec<String> },
    /// The instances differ in shape, or declare different results: the
    /// second is a chunk of its own, under the first's signature.
    Chunk { text: String, why: String },
}

struct Unifier<'a> {
    base: &'a Pattern,
    other: &'a Pattern,
    /// Placeholders of the second instance by those of the first.
    map: BTreeMap<PhId, PhId>,
    /// Placeholders of the first in use by the second (one to one).
    used: BTreeMap<PhId, PhId>,
    /// Fresh placeholders for constants that differ: (first, second) -> id.
    consts: BTreeMap<(i128, i128), PhId>,
    /// Names added to the first pattern.
    names: Vec<String>,
    notes: Vec<String>,
}

impl<'a> Unifier<'a> {
    fn fresh(&mut self, a: i128, b: i128) -> PhId {
        if let Some(id) = self.consts.get(&(a, b)) {
            return *id;
        }
        let n = self.consts.len() + 1;
        let mut name = format!("k{n}");
        while self.base.names.contains(&name) || self.names.contains(&name) {
            name.push('_');
        }
        let id = PhId((self.base.names.len() + self.names.len()) as u16);
        self.names.push(name.clone());
        self.consts.insert((a, b), id);
        self.notes.push(format!("${name} stands for {a:#x} in the first instance and {b:#x} in the second"));
        id
    }

    /// The first instance's placeholder `a` faces the second's `b`.
    fn placeholder(&mut self, a: PhId, b: PhId) -> Result<(), String> {
        match self.map.get(&b) {
            Some(mapped) if *mapped == a => Ok(()),
            Some(mapped) => Err(format!("${} of the second instance stands for ${} and ${}", self.other.ph_name(b), self.base.ph_name(*mapped), self.base.ph_name(a))),
            None => match self.used.get(&a) {
                Some(taken) => Err(format!("${} of the first instance faces both ${} and ${}", self.base.ph_name(a), self.other.ph_name(*taken), self.other.ph_name(b))),
                None => {
                    self.map.insert(b, a);
                    self.used.insert(a, b);
                    Ok(())
                }
            },
        }
    }

    /// The first instance's placeholder for the second's `b`, once the bodies
    /// are aligned.
    fn mapped(&self, b: PhId) -> Option<PhId> {
        self.map.get(&b).copied().or((b == RET).then_some(RET))
    }

    /// An expression of the second instance in the first's placeholders; a
    /// constant the bodies generalised becomes the same placeholder.
    fn translate(&self, e: &Expr) -> Result<Expr, String> {
        Ok(match e {
            Expr::Placeholder(p) => Expr::Placeholder(self.mapped(*p).ok_or_else(|| {
                format!("${} of the second instance does not occur in the first", self.other.ph_name(*p))
            })?),
            Expr::Const(c) => {
                let mut found = self.consts.iter().filter(|((_, b), _)| b == c).map(|(_, id)| *id);
                match (found.next(), found.next()) {
                    (Some(id), None) => Expr::Placeholder(id),
                    _ => Expr::Const(*c),
                }
            }
            Expr::Op(o) => Expr::Op(OpNode { op: o.op, size: o.size, args: o.args.iter().map(|a| self.translate(a)).collect::<Result<_, _>>()? }),
            Expr::Call(c) => Expr::Call(Box::new(CallExpr {
                target: self.translate(&c.target)?,
                args: c.args.iter().map(|a| self.translate(a)).collect::<Result<_, _>>()?,
                variadic: c.variadic,
            })),
            other => other.clone(),
        })
    }

    fn dest(&mut self, a: &Dest, b: &Dest) -> Result<Dest, String> {
        match (a, b) {
            (Dest::Ph(x), Dest::Ph(y)) => {
                self.placeholder(*x, *y)?;
                Ok(Dest::Ph(*x))
            }
            (Dest::Wildcard, _) | (_, Dest::Wildcard) => Ok(Dest::Wildcard),
        }
    }

    fn expr(&mut self, a: &Expr, b: &Expr) -> Result<Expr, String> {
        match (a, b) {
            (Expr::Placeholder(x), Expr::Placeholder(y)) => {
                self.placeholder(*x, *y)?;
                Ok(Expr::Placeholder(*x))
            }
            (Expr::Wildcard, _) | (_, Expr::Wildcard) => Ok(Expr::Wildcard),
            (Expr::Const(x), Expr::Const(y)) => {
                if x == y {
                    Ok(Expr::Const(*x))
                } else {
                    Ok(Expr::Placeholder(self.fresh(*x, *y)))
                }
            }
            (Expr::Symbol(x), Expr::Symbol(y)) if x.name == y.name => Ok(Expr::Symbol(x.clone())),
            (Expr::Op(x), Expr::Op(y)) if x.op == y.op && x.args.len() == y.args.len() => {
                let size = if x.size == y.size { x.size } else { None };
                if x.size != y.size {
                    self.notes.push(format!("the size of a {} differs between the instances and is left open", x.op.short_name().to_lowercase()));
                }
                let mut args = Vec::with_capacity(x.args.len());
                for (p, q) in x.args.iter().zip(&y.args) {
                    args.push(self.expr(p, q)?);
                }
                Ok(Expr::Op(OpNode { op: x.op, size, args }))
            }
            (Expr::Call(x), Expr::Call(y)) if x.args.len() == y.args.len() && x.variadic == y.variadic => {
                let target = self.expr(&x.target, &y.target)?;
                let mut args = Vec::with_capacity(x.args.len());
                for (p, q) in x.args.iter().zip(&y.args) {
                    args.push(self.expr(p, q)?);
                }
                Ok(Expr::Call(Box::new(CallExpr { target, args, variadic: x.variadic })))
            }
            _ => Err(format!("`{}` faces `{}`", format_expr(self.base, a), format_expr(self.other, b))),
        }
    }

    fn stmt(&mut self, a: &Stmt, b: &Stmt) -> Result<Stmt, String> {
        match (a, b) {
            (Stmt::SetVar { dest: da, src: sa }, Stmt::SetVar { dest: db, src: sb }) => {
                Ok(Stmt::SetVar { dest: self.dest(da, db)?, src: self.expr(sa, sb)? })
            }
            (Stmt::Store { size: za, dest: da, src: sa }, Stmt::Store { size: zb, dest: db, src: sb }) => {
                Ok(Stmt::Store { size: if za == zb { *za } else { None }, dest: self.expr(da, db)?, src: self.expr(sa, sb)? })
            }
            (Stmt::Call(x), Stmt::Call(y)) if x.outputs.len() == y.outputs.len() && x.args.len() == y.args.len() => {
                let mut outputs = Vec::new();
                for (p, q) in x.outputs.iter().zip(&y.outputs) {
                    outputs.push(self.dest(p, q)?);
                }
                let target = self.expr(&x.target, &y.target)?;
                let mut args = Vec::new();
                for (p, q) in x.args.iter().zip(&y.args) {
                    args.push(self.expr(p, q)?);
                }
                Ok(Stmt::Call(crate::pattern::CallStmt { outputs, target, args, variadic: x.variadic || y.variadic, extra_outputs: x.extra_outputs || y.extra_outputs }))
            }
            (Stmt::Intrinsic(x), Stmt::Intrinsic(y)) if x.name.name == y.name.name && x.outputs.len() == y.outputs.len() && x.args.len() == y.args.len() => {
                let mut outputs = Vec::new();
                for (p, q) in x.outputs.iter().zip(&y.outputs) {
                    outputs.push(self.dest(p, q)?);
                }
                let mut args = Vec::new();
                for (p, q) in x.args.iter().zip(&y.args) {
                    args.push(self.expr(p, q)?);
                }
                Ok(Stmt::Intrinsic(IntrinsicStmt { outputs, name: x.name.clone(), args, variadic: x.variadic || y.variadic, extra_outputs: x.extra_outputs || y.extra_outputs }))
            }
            (Stmt::Ret(x), Stmt::Ret(y)) if x.len() == y.len() => {
                let mut values = Vec::new();
                for (p, q) in x.iter().zip(y) {
                    values.push(self.expr(p, q)?);
                }
                Ok(Stmt::Ret(values))
            }
            (Stmt::Nop, Stmt::Nop) => Ok(Stmt::Nop),
            (Stmt::If { cond: ca, t: ta, f: fa }, Stmt::If { cond: cb, .. }) => {
                // Labels are positional: the blocks are aligned by order.
                Ok(Stmt::If { cond: self.expr(ca, cb)?, t: *ta, f: *fa })
            }
            (Stmt::Goto(l), Stmt::Goto(_)) => Ok(Stmt::Goto(*l)),
            (Stmt::Expr(x), Stmt::Expr(y)) => Ok(Stmt::Expr(self.expr(x, y)?)),
            _ => Err(format!("`{}` faces `{}`", crate::pattern::format_stmt(self.base, a), crate::pattern::format_stmt(self.other, b))),
        }
    }
}

use crate::pattern::format_expr;

/// The function a pattern describes, as its signature names it.
fn own_name(p: &Pattern) -> Option<String> {
    let title = chunk_title(&format!("signature: {}", p.signature.as_deref()?));
    title.split_once('(').map(|(name, _)| name.to_string())
}

/// `e` with its calls to `from` made calls to `to`.
fn retarget(e: &Expr, from: &str, to: &str) -> Expr {
    match e {
        Expr::Call(c) => {
            let target = match &c.target {
                Expr::Symbol(s) if s.name == from => Expr::Symbol(SymbolRef { name: to.to_string() }),
                t => retarget(t, from, to),
            };
            Expr::Call(Box::new(CallExpr { target, args: c.args.iter().map(|a| retarget(a, from, to)).collect(), variadic: c.variadic }))
        }
        Expr::Op(o) => Expr::Op(OpNode { op: o.op, size: o.size, args: o.args.iter().map(|a| retarget(a, from, to)).collect() }),
        other => other.clone(),
    }
}

/// Generalises `base`, the pattern being extended (edited or not), with a
/// second instance `other` (a pattern drafted from the second region).  The
/// signature, type constraints and `result:` lines of `base` are kept;
/// `value:`, `branch:` and `result:` lines both have are generalised like the
/// body, a `result:` line only `other` has is added, and instances whose
/// declarations conflict stay separate chunks.
pub fn generalize(base: &Pattern, other: &Pattern) -> Generalized {
    // A draft calls its function by a name of its own (`outlined`); its header
    // lines speak of the first pattern's function once they join it.
    let names = (own_name(base), own_name(other));
    let renamed = |e: &Expr| match &names {
        (Some(to), Some(from)) if to != from => retarget(e, from, to),
        _ => e.clone(),
    };
    let chunk = |why: String| {
        // The second instance as a shape of its own, under the first's signature.
        let mut second = other.clone();
        second.signature = base.signature.clone();
        second.pure = base.pure;
        second.value = other.value.as_ref().map(renamed);
        second.branch = other.branch.as_ref().map(renamed);
        second.results = other.results.iter().map(|(n, e)| (*n, renamed(e))).collect();
        Generalized::Chunk { text: format_pattern(&second), why }
    };
    if base.blocks.len() != other.blocks.len() {
        return chunk(format!("the instances have {} and {} blocks", base.blocks.len(), other.blocks.len()));
    }
    let mut u = Unifier { base, other, map: BTreeMap::new(), used: BTreeMap::new(), consts: BTreeMap::new(), names: Vec::new(), notes: Vec::new() };
    let mut blocks: Vec<Block> = Vec::with_capacity(base.blocks.len());
    for (k, (a, b)) in base.blocks.iter().zip(&other.blocks).enumerate() {
        if a.stmts.len() != b.stmts.len() {
            return chunk(format!("block {} has {} statements in the first instance and {} in the second", k + 1, a.stmts.len(), b.stmts.len()));
        }
        let mut stmts = Vec::with_capacity(a.stmts.len());
        for (p, q) in a.stmts.iter().zip(&b.stmts) {
            match u.stmt(p, q) {
                Ok(s) => stmts.push(s),
                Err(why) => return chunk(why),
            }
        }
        blocks.push(Block { label: a.label, stmts, line: a.line, stmt_lines: Vec::new() });
    }
    // The header lines, generalised the same way.
    let mut line = |a: &Option<Expr>, b: &Option<Expr>, what: &str| -> Result<Option<Expr>, String> {
        match (a, b) {
            (None, None) => Ok(None),
            (Some(a), Some(b)) => u.expr(a, &renamed(b)).map(Some).map_err(|why| format!("the {what} lines differ: {why}")),
            _ => Err(format!("only one of the instances has a {what} line")),
        }
    };
    let value = match line(&base.value, &other.value, "value:") {
        Ok(v) => v,
        Err(why) => return chunk(why),
    };
    let branch = match line(&base.branch, &other.branch, "branch:") {
        Ok(b) => b,
        Err(why) => return chunk(why),
    };
    let mut results: Vec<(PhId, Expr)> = Vec::new();
    for (name, a) in &base.results {
        let counterpart = other.results.iter().find(|(n, _)| u.mapped(*n) == Some(*name));
        match counterpart {
            Some((_, b)) => match u.expr(a, &renamed(b)) {
                Ok(e) => results.push((*name, e)),
                Err(why) => return chunk(format!("the instances declare different results for ${}: {why}", base.ph_name(*name))),
            },
            // The first pattern is the one the user edited: a line of its own stays,
            // including what $ret holds, as long as the second instance's $ret is the
            // same variable of the aligned bodies.
            None if *name == RET && u.map.get(&RET) != Some(&RET) => {
                return chunk("only the first instance has a 'result:' line for $ret, and the instances' $ret differ".to_string())
            }
            None => results.push((*name, a.clone())),
        }
    }
    for (name, b) in &other.results {
        let mapped = u.mapped(*name);
        if mapped.is_some_and(|m| base.results.iter().any(|(n, _)| *n == m)) {
            continue;
        }
        let Some(mapped) = mapped.filter(|m| *m != RET) else {
            return chunk(format!("only the second instance has a 'result:' line for ${}", other.ph_name(*name)));
        };
        match u.translate(&renamed(b)) {
            Ok(e) => {
                u.notes.push(format!("added the second instance's 'result:' line for ${}", base.ph_name(mapped)));
                results.push((mapped, e));
            }
            Err(why) => return chunk(why),
        }
    }
    let mut merged = base.clone();
    merged.blocks = blocks;
    merged.value = value;
    merged.branch = branch;
    merged.results = results;
    merged.names.extend(u.names.iter().cloned());
    merged.types.resize(merged.names.len(), None);
    Generalized::Merged { text: format_pattern(&merged), notes: u.notes }
}
