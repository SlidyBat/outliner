//! The text pattern language: a small piece of MLIL written the way Binary
//! Ninja prints it, with `$name` placeholders where the real code may contain
//! any expression or variable.  See the README for the syntax.
//!
//! This module holds the syntax tree and the questions the matcher asks of a
//! pattern; parsing lives in [`parser`], the pattern file format in [`chunks`].

pub mod chunks;
pub mod lexer;
pub mod parser;
pub mod print;

use std::fmt;

use crate::ops::Op;

pub use chunks::{chunk_key, chunk_title, join_chunks, split_chunks, ChunkSet};
pub use print::{format_expr, format_pattern, format_stmt};
pub use parser::{parse_function_text, parse_pattern};

/// The reserved placeholder that receives the outlined call's result.
pub const RESULT_NAME: &str = "ret";
/// Its id: every pattern interns `ret` first.
pub const RET: PhId = PhId(0);
/// The most placeholders one chunk may declare.
pub const MAX_PLACEHOLDERS: usize = 128;

/// A placeholder, by its index in the chunk's name table.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PhId(pub u16);

/// A label, by its index in the pattern's label table.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LabelId(pub u16);

/// A set of placeholders.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct PhSet(pub u128);

impl PhSet {
    pub fn insert(&mut self, id: PhId) {
        self.0 |= 1u128 << id.0;
    }

    pub fn contains(self, id: PhId) -> bool {
        self.0 & (1u128 << id.0) != 0
    }

    pub fn union(self, other: PhSet) -> PhSet {
        PhSet(self.0 | other.0)
    }

    pub fn is_subset(self, other: PhSet) -> bool {
        self.0 & !other.0 == 0
    }

    pub fn iter(self) -> impl Iterator<Item = PhId> {
        (0..128u16).filter(move |k| self.0 & (1u128 << k) != 0).map(PhId)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PatternError(pub String);

impl fmt::Display for PatternError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for PatternError {}

pub type Result<T> = std::result::Result<T, PatternError>;

fn err<T>(msg: impl Into<String>) -> Result<T> {
    Err(PatternError(msg.into()))
}

// --------------------------------------------------------------------------- AST

/// A symbol named in a pattern; a quoted name with `*` or `?` matches any of
/// an address's names by glob.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymbolRef {
    pub name: String,
}

impl SymbolRef {
    pub fn is_glob(&self) -> bool {
        self.name.contains('*') || self.name.contains('?')
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpNode {
    pub op: Op,
    /// None: unconstrained.
    pub size: Option<u16>,
    pub args: Vec<Expr>,
}

/// `call(target, args...)` used inside an expression: the result of a call.
/// Matches a variable whose definition is that call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallExpr {
    pub target: Expr,
    pub args: Vec<Expr>,
    pub variadic: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Placeholder(PhId),
    Wildcard,
    Const(i128),
    Symbol(SymbolRef),
    Op(OpNode),
    Call(Box<CallExpr>),
}

impl Expr {
    pub fn op(op: Op, size: Option<u16>, args: Vec<Expr>) -> Expr {
        Expr::Op(OpNode { op, size, args })
    }

    pub fn as_op(&self) -> Option<&OpNode> {
        match self {
            Expr::Op(o) => Some(o),
            _ => None,
        }
    }

    pub fn as_placeholder(&self) -> Option<PhId> {
        match self {
            Expr::Placeholder(p) => Some(*p),
            _ => None,
        }
    }

    pub fn as_const(&self) -> Option<i128> {
        match self {
            Expr::Const(c) => Some(*c),
            _ => None,
        }
    }

    pub fn as_call(&self) -> Option<&CallExpr> {
        match self {
            Expr::Call(c) => Some(c),
            _ => None,
        }
    }
}

/// The target of an assignment or a call output.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Dest {
    Ph(PhId),
    Wildcard,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallStmt {
    pub outputs: Vec<Dest>,
    pub target: Expr,
    pub args: Vec<Expr>,
    pub variadic: bool,
    /// The code's call may have more outputs than listed (`$r, ... = call(...)`).
    pub extra_outputs: bool,
}

/// `outputs = intrinsic("name", args)`: an architecture intrinsic, named as
/// the architecture names it (a quoted string, wildcards allowed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntrinsicStmt {
    pub outputs: Vec<Dest>,
    pub name: SymbolRef,
    pub args: Vec<Expr>,
    pub variadic: bool,
    /// The code's intrinsic may have more outputs than listed (`$r, ... = intrinsic(...)`).
    pub extra_outputs: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    SetVar { dest: Dest, src: Expr },
    Store { size: Option<u16>, dest: Expr, src: Expr },
    Call(CallStmt),
    Intrinsic(IntrinsicStmt),
    Ret(Vec<Expr>),
    Nop,
    If { cond: Expr, t: LabelId, f: LabelId },
    Goto(LabelId),
    /// A statement written in the generic `op.size(operands)` form (always an `Expr::Op`).
    Expr(Expr),
}

impl Stmt {
    pub fn is_terminator(&self) -> bool {
        match self {
            Stmt::If { .. } | Stmt::Goto(_) | Stmt::Ret(_) => true,
            Stmt::Expr(Expr::Op(o)) => o.op == Op::Noret,
            Stmt::Expr(_) => false,
            _ => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub label: Option<LabelId>,
    pub stmts: Vec<Stmt>,
    pub line: u32,
    /// The source line of each statement (parallel to `stmts`; empty for built patterns).
    pub stmt_lines: Vec<u32>,
}

impl Block {
    /// The statement that ends the block: a branch, a return, or `noret()`.
    pub fn terminator(&self) -> Option<&Stmt> {
        self.stmts.last().filter(|s| s.is_terminator())
    }
}

/// `rewrite: lhs => rhs [when cond]`: where the code is spelled like `lhs` the
/// matcher may read it as `rhs`.  A rule has a placeholder namespace of its own.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule {
    pub lhs: Expr,
    pub rhs: Expr,
    pub when: Option<Expr>,
    pub text: String,
    pub names: Vec<String>,
}

impl Rule {
    /// The operation the left side matches, when it is one (they all are).
    pub fn lhs_op(&self) -> Option<Op> {
        self.lhs.as_op().map(|o| o.op)
    }
}

/// An integer position in a byte image: a placeholder or a constant.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum IntArg {
    Ph(PhId),
    Const(i128),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LenArg {
    Ph(PhId),
    Const(i128),
    Wildcard,
}

/// The parts of `set_var_field($v, off, const_data($chars, $n))`: a run of
/// constant stores into `$v` spelling `$n` characters and a terminator from
/// offset `off`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ImageStore {
    pub dest: PhId,
    pub offset: IntArg,
    /// None: `_`.
    pub chars: Option<PhId>,
    pub length: LenArg,
}

/// The byte image a statement stands for, None for any other statement.  An
/// error when `const_data` is used in a body statement any other way.
pub fn image_store(stmt: &Stmt) -> Result<Option<ImageStore>> {
    let value = match stmt {
        Stmt::Expr(Expr::Op(o)) if o.op == Op::SetVarField && o.args.len() == 3 => match &o.args[2] {
            Expr::Op(v) if v.op == Op::ConstData => Some((o, v)),
            _ => None,
        },
        _ => None,
    };
    let Some((op, value)) = value else {
        if mentions_op_stmt(stmt, Op::ConstData) {
            return err("in a statement const_data(...) may only be the value of set_var_field($v, offset, const_data($chars, $n))");
        }
        return Ok(None);
    };
    if op.size.is_some() {
        return err("set_var_field with const_data takes no size: the stores spelling the text have their own");
    }
    let bad = || err("a byte image is written set_var_field($v, offset, const_data($chars, $n)) with a placeholder or constant offset and a placeholder or constant count");
    let Some(dest) = op.args[0].as_placeholder() else { return bad() };
    let offset = match &op.args[1] {
        Expr::Placeholder(p) => IntArg::Ph(*p),
        Expr::Const(c) => IntArg::Const(*c),
        _ => return bad(),
    };
    if value.args.len() != 2 {
        return bad();
    }
    let chars = match &value.args[0] {
        Expr::Placeholder(p) => Some(*p),
        Expr::Wildcard => None,
        _ => return bad(),
    };
    let length = match &value.args[1] {
        Expr::Placeholder(p) => LenArg::Ph(*p),
        Expr::Const(c) => LenArg::Const(*c),
        Expr::Wildcard => LenArg::Wildcard,
        _ => return bad(),
    };
    if let LenArg::Const(c) = length {
        if c < 1 {
            return err("const_data needs at least one character");
        }
    }
    Ok(Some(ImageStore { dest, offset, chars, length }))
}

pub fn mentions_op(expr: &Expr, op: Op) -> bool {
    match expr {
        Expr::Op(o) => o.op == op || o.args.iter().any(|a| mentions_op(a, op)),
        Expr::Call(c) => mentions_op(&c.target, op) || c.args.iter().any(|a| mentions_op(a, op)),
        _ => false,
    }
}

fn mentions_op_stmt(stmt: &Stmt, op: Op) -> bool {
    match stmt {
        Stmt::SetVar { src, .. } => mentions_op(src, op),
        Stmt::Store { dest, src, .. } => mentions_op(dest, op) || mentions_op(src, op),
        Stmt::Call(c) => mentions_op(&c.target, op) || c.args.iter().any(|a| mentions_op(a, op)),
        Stmt::Intrinsic(c) => c.args.iter().any(|a| mentions_op(a, op)),
        Stmt::Ret(values) => values.iter().any(|v| mentions_op(v, op)),
        Stmt::If { cond, .. } => mentions_op(cond, op),
        Stmt::Expr(e) => mentions_op(e, op),
        Stmt::Nop | Stmt::Goto(_) => false,
    }
}

/// The logical negation of a comparison, or None if `expr` is not one.
pub fn negate(expr: &Expr) -> Option<Expr> {
    match expr {
        Expr::Op(o) => o.op.complement().map(|c| Expr::op(c, o.size, o.args.clone())),
        _ => None,
    }
}

pub fn collect_placeholders(expr: &Expr, out: &mut PhSet) {
    match expr {
        Expr::Placeholder(p) => out.insert(*p),
        Expr::Op(o) => o.args.iter().for_each(|a| collect_placeholders(a, out)),
        Expr::Call(c) => {
            collect_placeholders(&c.target, out);
            c.args.iter().for_each(|a| collect_placeholders(a, out));
        }
        _ => {}
    }
}

pub fn collect_placeholders_stmt(stmt: &Stmt, out: &mut PhSet) {
    match stmt {
        Stmt::SetVar { dest, src } => {
            if let Dest::Ph(p) = dest {
                out.insert(*p);
            }
            collect_placeholders(src, out);
        }
        Stmt::Store { dest, src, .. } => {
            collect_placeholders(dest, out);
            collect_placeholders(src, out);
        }
        Stmt::Call(c) => {
            for o in &c.outputs {
                if let Dest::Ph(p) = o {
                    out.insert(*p);
                }
            }
            collect_placeholders(&c.target, out);
            c.args.iter().for_each(|a| collect_placeholders(a, out));
        }
        Stmt::Intrinsic(c) => {
            for o in &c.outputs {
                if let Dest::Ph(p) = o {
                    out.insert(*p);
                }
            }
            c.args.iter().for_each(|a| collect_placeholders(a, out));
        }
        Stmt::Ret(values) => values.iter().for_each(|v| collect_placeholders(v, out)),
        Stmt::If { cond, .. } => collect_placeholders(cond, out),
        Stmt::Expr(e) => collect_placeholders(e, out),
        Stmt::Nop | Stmt::Goto(_) => {}
    }
}

pub fn collect_calls<'a>(expr: &'a Expr, out: &mut Vec<&'a CallExpr>) {
    match expr {
        Expr::Call(c) => {
            out.push(c);
            c.args.iter().for_each(|a| collect_calls(a, out));
        }
        Expr::Op(o) => o.args.iter().for_each(|a| collect_calls(a, out)),
        _ => {}
    }
}

pub fn contains_call(expr: &Expr) -> bool {
    match expr {
        Expr::Call(_) => true,
        Expr::Op(o) => o.args.iter().any(contains_call),
        _ => false,
    }
}

// --------------------------------------------------------------------------- pattern

/// A pattern seen as `guard ? true_arm : false_arm`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GuardedValue {
    pub guard: Expr,
    pub true_arm: Expr,
    pub false_arm: Expr,
}

/// A void pattern seen as `if guard then {true_arm} else {false_arm}`:
/// statement runs one call stands for (one of them empty for a triangle).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GuardedStatements {
    pub guard: Expr,
    pub true_arm: Vec<Stmt>,
    pub false_arm: Vec<Stmt>,
}

/// A type constraint on a placeholder: a C type, or a `/regex/` over the printed type.
#[derive(Clone, Debug)]
pub struct TypeConstraint {
    pub text: String,
    regex: Option<fancy_regex::Regex>,
}

impl TypeConstraint {
    pub fn new(text: &str) -> TypeConstraint {
        let regex = if text.len() >= 2 && text.starts_with('/') && text.ends_with('/') {
            fancy_regex::Regex::new(&text[1..text.len() - 1]).ok()
        } else {
            None
        };
        TypeConstraint { text: text.to_string(), regex }
    }

    pub fn is_regex(&self) -> bool {
        self.text.len() >= 2 && self.text.starts_with('/') && self.text.ends_with('/')
    }

    /// For a regex constraint: whether the printed type matches it (a regex that
    /// does not compile matches nothing).
    pub fn regex_matches(&self, type_text: &str) -> bool {
        match &self.regex {
            Some(re) => re.is_match(type_text).unwrap_or(false),
            None => false,
        }
    }
}

impl PartialEq for TypeConstraint {
    fn eq(&self, other: &Self) -> bool {
        self.text == other.text
    }
}

impl Eq for TypeConstraint {}

#[derive(Clone, Debug)]
pub struct Pattern {
    pub blocks: Vec<Block>,
    /// Placeholder names by [`PhId`]; `names[0]` is `ret`.
    pub names: Vec<String>,
    /// Label names by [`LabelId`].
    pub labels: Vec<String>,
    /// Type constraints by [`PhId`].
    pub types: Vec<Option<TypeConstraint>>,
    pub signature: Option<String>,
    pub source: String,
    /// From the signature's `__pure` attribute.
    pub pure: bool,
    /// `value:` patterns match this expression anywhere.
    pub value: Option<Expr>,
    /// `result:` lines: (placeholder, expression).
    pub results: Vec<(PhId, Expr)>,
    /// `branch:`: condition of the exit branch after the call.
    pub branch: Option<Expr>,
    /// A rules chunk: rewrite rules only.
    pub rules: Vec<Rule>,
    pub rules_name: Option<String>,
    // Filled in once the signature has been parsed by the host:
    pub name: String,
    pub params: Vec<String>,
    pub returns: bool,
    guarded_value: Option<GuardedValue>,
    guarded_statements: Option<GuardedStatements>,
}

impl Pattern {
    pub(crate) fn new(
        blocks: Vec<Block>,
        names: Vec<String>,
        labels: Vec<String>,
        types: Vec<Option<TypeConstraint>>,
        signature: Option<String>,
        source: String,
        value: Option<Expr>,
        results: Vec<(PhId, Expr)>,
        branch: Option<Expr>,
        rules: Vec<Rule>,
        rules_name: Option<String>,
    ) -> Pattern {
        let mut p = Pattern {
            blocks,
            names,
            labels,
            types,
            signature,
            source,
            pure: false,
            value,
            results,
            branch,
            rules,
            rules_name,
            name: String::new(),
            params: Vec::new(),
            returns: false,
            guarded_value: None,
            guarded_statements: None,
        };
        p.guarded_value = p.compute_guarded_value();
        p
    }

    pub fn is_rules(&self) -> bool {
        !self.rules.is_empty()
    }

    // -- names -----------------------------------------------------------------
    pub fn ph(&self, name: &str) -> Option<PhId> {
        self.names.iter().position(|n| n == name).map(|i| PhId(i as u16))
    }

    pub fn ph_name(&self, id: PhId) -> &str {
        &self.names[id.0 as usize]
    }

    pub fn ph_count(&self) -> usize {
        self.names.len()
    }

    pub fn label(&self, name: &str) -> Option<LabelId> {
        self.labels.iter().position(|n| n == name).map(|i| LabelId(i as u16))
    }

    pub fn label_name(&self, id: LabelId) -> &str {
        &self.labels[id.0 as usize]
    }

    pub fn type_of(&self, id: PhId) -> Option<&TypeConstraint> {
        self.types.get(id.0 as usize).and_then(|t| t.as_ref())
    }

    pub fn block_by_label(&self, label: LabelId) -> Option<&Block> {
        self.blocks.iter().find(|b| b.label == Some(label))
    }

    /// The labels that name a block.
    pub fn defined_labels(&self) -> Vec<LabelId> {
        self.blocks.iter().filter_map(|b| b.label).collect()
    }

    // -- shapes ----------------------------------------------------------------
    /// If the pattern is a plain diamond (`if G then a else b`, each arm
    /// `$ret = X; goto done`, `done:` empty) return it as a guarded value.
    pub fn guarded_value(&self) -> Option<&GuardedValue> {
        self.guarded_value.as_ref()
    }

    fn compute_guarded_value(&self) -> Option<GuardedValue> {
        let blocks = &self.blocks;
        if self.value.is_some() || blocks.len() != 4 {
            return None;
        }
        let entry = &blocks[0].stmts;
        let Some(Stmt::If { cond, t, f }) = entry.first() else { return None };
        if entry.len() != 1 || t == f {
            return None;
        }
        let done = blocks[3].label?;
        let mut arms: Vec<(LabelId, &Expr)> = Vec::new();
        for block in &blocks[1..3] {
            if block.stmts.len() != 2 {
                return None;
            }
            let src = match &block.stmts[0] {
                Stmt::SetVar { dest: Dest::Ph(p), src } if *p == RET => src,
                _ => return None,
            };
            match &block.stmts[1] {
                Stmt::Goto(l) if *l == done => {}
                _ => return None,
            }
            arms.push((block.label?, src));
        }
        if !blocks[3].stmts.is_empty() {
            return None;
        }
        let arm = |l: LabelId| arms.iter().find(|(x, _)| *x == l).map(|(_, e)| (*e).clone());
        Some(GuardedValue { guard: cond.clone(), true_arm: arm(*t)?, false_arm: arm(*f)? })
    }

    /// If the pattern is a void diamond (`if G then {stmts} else {stmts}`, each
    /// arm ending in `goto done`, `done:` empty) or triangle (one side of the
    /// `if` goes straight to `done`) with a `result:` call, return its arms as
    /// statement runs.
    pub fn guarded_statements(&self) -> Option<&GuardedStatements> {
        self.guarded_statements.as_ref()
    }

    fn compute_guarded_statements(&self) -> Option<GuardedStatements> {
        let blocks = &self.blocks;
        if self.value.is_some() || !(3..=4).contains(&blocks.len()) || self.returns || self.result_call().is_none() {
            return None;
        }
        let entry = &blocks[0].stmts;
        let Some(Stmt::If { cond, t, f }) = entry.first() else { return None };
        if entry.len() != 1 || t == f {
            return None;
        }
        let done = blocks.last()?;
        let done_label = done.label?;
        if !done.stmts.is_empty() {
            return None;
        }
        let mut arms: Vec<(LabelId, Vec<Stmt>)> = vec![(done_label, Vec::new())];
        for block in &blocks[1..blocks.len() - 1] {
            match block.stmts.last() {
                Some(Stmt::Goto(l)) if *l == done_label => {}
                _ => return None,
            }
            arms.push((block.label?, block.stmts[..block.stmts.len() - 1].to_vec()));
        }
        let arm = |l: LabelId| arms.iter().find(|(x, _)| *x == l).map(|(_, s)| s.clone());
        Some(GuardedStatements { guard: cond.clone(), true_arm: arm(*t)?, false_arm: arm(*f)? })
    }

    // -- introspection ---------------------------------------------------------
    /// Placeholders the statements (or the `value:` expression) bind.
    pub fn body_placeholders(&self) -> PhSet {
        let mut found = PhSet::default();
        for block in &self.blocks {
            for stmt in &block.stmts {
                collect_placeholders_stmt(stmt, &mut found);
            }
        }
        if let Some(v) = &self.value {
            collect_placeholders(v, &mut found);
        }
        found
    }

    pub fn placeholders(&self) -> PhSet {
        let mut found = self.body_placeholders();
        for (_, expr) in &self.results {
            collect_placeholders(expr, &mut found);
        }
        if let Some(b) = &self.branch {
            collect_placeholders(b, &mut found);
        }
        found
    }

    /// With `branch:`, the label the pattern leaves through: the one target of
    /// its `if` statements that names no block of the pattern.
    pub fn exit_branch(&self) -> Option<LabelId> {
        self.branch.as_ref()?;
        let defined = self.defined_labels();
        let mut external: Vec<LabelId> = Vec::new();
        for block in &self.blocks {
            if let Some(Stmt::If { t, f, .. }) = block.terminator() {
                for target in [*t, *f] {
                    if !defined.contains(&target) && !external.contains(&target) {
                        external.push(target);
                    }
                }
            }
        }
        if external.len() == 1 {
            Some(external[0])
        } else {
            None
        }
    }

    /// The `result:` expression for `$ret`, if any.
    pub fn result(&self) -> Option<&Expr> {
        self.result_expr(RET)
    }

    pub fn result_expr(&self, id: PhId) -> Option<&Expr> {
        self.results.iter().find(|(n, _)| *n == id).map(|(_, e)| e)
    }

    /// The call to this pattern's own function inside the `result:` lines.
    pub fn result_call(&self) -> Option<&CallExpr> {
        for (_, expr) in &self.results {
            let mut calls = Vec::new();
            collect_calls(expr, &mut calls);
            if let Some(c) = calls.first() {
                return Some(c);
            }
        }
        None
    }

    /// The placeholders the call's arguments come from, in parameter order: the
    /// parameters themselves unless `result:` names the arguments.
    pub fn argument_placeholders(&self) -> Vec<PhId> {
        let Some(call) = self.result_call() else {
            return self.params.iter().filter_map(|p| self.ph(p)).collect();
        };
        let mut names: Vec<PhId> = Vec::new();
        for a in &call.args {
            let mut found = PhSet::default();
            match a {
                Expr::Placeholder(p) => found.insert(*p),
                Expr::Op(_) => collect_placeholders(a, &mut found),
                _ => continue,
            }
            for n in found.iter() {
                if !names.contains(&n) {
                    names.push(n);
                }
            }
        }
        names
    }

    /// Placeholders passed by address (`&$v` in `result:`).
    pub fn reference_placeholders(&self) -> PhSet {
        let mut out = PhSet::default();
        if let Some(call) = self.result_call() {
            for a in &call.args {
                if let Expr::Op(o) = a {
                    if o.op == Op::AddressOf {
                        if let Some(Expr::Placeholder(p)) = o.args.first() {
                            out.insert(*p);
                        }
                    }
                }
            }
        }
        out
    }

    /// Placeholders whose variables receive a value at the call: `$ret` and
    /// every `result: $name = ...` line.
    pub fn output_placeholders(&self) -> PhSet {
        let mut out = PhSet::default();
        for (n, _) in &self.results {
            out.insert(*n);
        }
        if self.returns {
            out.insert(RET);
        }
        out
    }

    /// True when `$ret` holds the call's own value, so the call can write the code's variable directly.
    pub fn ret_is_call(&self) -> bool {
        match self.result_expr(RET) {
            None => true,
            Some(Expr::Call(_)) => true,
            Some(Expr::Placeholder(p)) => *p == RET,
            _ => false,
        }
    }

    pub fn assigned_placeholders(&self) -> PhSet {
        let mut found = PhSet::default();
        for block in &self.blocks {
            for stmt in &block.stmts {
                match stmt {
                    Stmt::SetVar { dest: Dest::Ph(p), .. } => found.insert(*p),
                    Stmt::Call(c) => {
                        for o in &c.outputs {
                            if let Dest::Ph(p) = o {
                                found.insert(*p);
                            }
                        }
                    }
                    Stmt::Intrinsic(c) => {
                        for o in &c.outputs {
                            if let Dest::Ph(p) = o {
                                found.insert(*p);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        found
    }

    /// The placeholder each signature parameter binds, None for one the pattern
    /// never mentions (a `result:` constant stands for it).
    pub fn param_ids(&self) -> Vec<Option<PhId>> {
        self.params.iter().map(|p| self.ph(p)).collect()
    }

    /// Check the pattern against the parsed signature's parameter names and
    /// whether it returns a value; `pure` is the signature's `__pure` attribute
    /// and `name` its function name (checked against `result:` when given).
    pub fn validate_signature(&mut self, params: &[String], returns: bool, pure: bool, name: Option<&str>) -> Result<()> {
        let used = self.placeholders();
        let mut assigned = self.assigned_placeholders();
        if self.value.is_some() {
            if !returns {
                return err("a 'value:' pattern needs a signature that returns a value");
            }
            if used.contains(RET) {
                return err(format!("${RESULT_NAME} has no meaning in a 'value:' pattern"));
            }
            assigned = PhSet::default();
            assigned.insert(RET);
        }
        // Parameters the result: call passes as constants.
        let mut specialised: Vec<&str> = Vec::new();
        if let Some(call) = self.result_call() {
            if !returns
                && (self.results.len() != 1 || self.results[0].0 != RET || !matches!(self.results[0].1, Expr::Call(_)))
            {
                return err("for a void function the only 'result:' line allowed is the bare call");
            }
            if let Some(name) = name {
                match &call.target {
                    Expr::Symbol(s) if s.name == name => {}
                    _ => return err(format!("the call in 'result:' must be to this pattern's own function '{name}'")),
                }
            }
            if call.args.len() != params.len() {
                return err(format!(
                    "the call in 'result:' passes {} argument(s) but the signature has {} parameter(s)",
                    call.args.len(),
                    params.len()
                ));
            }
            let bound = self.body_placeholders();
            for (param, arg) in params.iter().zip(&call.args) {
                let arg = match arg {
                    Expr::Const(_) => {
                        specialised.push(param);
                        continue;
                    }
                    Expr::Op(o) if o.op == Op::ConstData => {
                        if o.args.len() != 2
                            || !matches!(o.args[1], Expr::Const(_) | Expr::Placeholder(_))
                            || !matches!(o.args[0], Expr::Placeholder(_) | Expr::Const(_))
                        {
                            return err("const_data takes a placeholder or constant and a character count (a constant or a placeholder)");
                        }
                        if let Expr::Const(count) = o.args[1] {
                            if !(1..=8).contains(&count) {
                                return err("a constant const_data count is 1 to 8 characters (what a register holds); longer text needs a count the pattern binds from the stores that spell it");
                            }
                        }
                        if let Expr::Placeholder(count) = o.args[1] {
                            if !bound.contains(count) {
                                return err(format!(
                                    "'result:' passes const_data with ${}, which the pattern never binds",
                                    self.ph_name(count)
                                ));
                            }
                        }
                        specialised.push(param);
                        match &o.args[0] {
                            Expr::Placeholder(_) => &o.args[0],
                            _ => continue,
                        }
                    }
                    Expr::Op(o) if o.op == Op::AddressOf && matches!(o.args.first(), Some(Expr::Placeholder(_))) => {
                        &o.args[0]
                    }
                    Expr::Op(_) => {
                        // An expression over bound placeholders (`$pos + 1`) for a value
                        // the code never holds in a variable of its own.
                        let mut names = PhSet::default();
                        collect_placeholders(arg, &mut names);
                        if names == PhSet::default() || names.contains(RET) {
                            return err(format!(
                                "an expression argument in 'result:' must use placeholders the pattern binds, not ${RESULT_NAME}"
                            ));
                        }
                        for n in names.iter() {
                            if !bound.contains(n) {
                                return err(format!("'result:' passes ${}, which the pattern never binds", self.ph_name(n)));
                            }
                        }
                        continue;
                    }
                    other => other,
                };
                let Expr::Placeholder(p) = arg else {
                    return err("arguments in 'result:' must be placeholders, &placeholders, const_data(...), expressions over placeholders or constants");
                };
                if *p == RET {
                    return err("arguments in 'result:' must be placeholders, &placeholders, const_data(...), expressions over placeholders or constants");
                }
                if !bound.contains(*p) {
                    return err(format!("'result:' passes ${}, which the pattern never binds", self.ph_name(*p)));
                }
            }
            for (line_name, expr) in &self.results {
                if *line_name == RET {
                    if !matches!(expr, Expr::Call(_)) && !assigned.contains(RET) {
                        return err(format!("'result:' rewrites ${RESULT_NAME} but the pattern never assigns it"));
                    }
                } else if !assigned.contains(*line_name) {
                    return err(format!("'result:' names ${} but the pattern never assigns it", self.ph_name(*line_name)));
                }
            }
        }
        if let Some(branch) = &self.branch {
            if !returns {
                return err("'branch:' needs a signature that returns a value");
            }
            let mut names = PhSet::default();
            collect_placeholders(branch, &mut names);
            let mut allowed = self.body_placeholders();
            allowed.insert(RET);
            for (n, _) in &self.results {
                allowed.insert(*n);
            }
            if !names.is_subset(allowed) {
                return err("'branch:' may only use $ret, declared outputs and placeholders the pattern binds");
            }
        }
        for p in params {
            if p == RESULT_NAME {
                return err(format!("a parameter may not be named '{RESULT_NAME}'"));
            }
            if p.is_empty() {
                return err("every parameter in the signature needs a name");
            }
            let mentioned = self.ph(p).map(|id| used.contains(id)).unwrap_or(false);
            if !mentioned && !specialised.contains(&p.as_str()) {
                return err(format!("parameter '{p}' of the signature never appears in the pattern as ${p}"));
            }
        }
        if returns && !assigned.contains(RET) && self.results.is_empty() {
            return err(format!("the signature returns a value but the pattern never assigns ${RESULT_NAME}"));
        }
        if !returns && used.contains(RET) {
            return err(format!("${RESULT_NAME} is used but the signature returns void"));
        }
        for (k, t) in self.types.iter().enumerate() {
            if t.is_some() && !used.contains(PhId(k as u16)) {
                return err(format!("type constraint for unused placeholder ${}", self.names[k]));
            }
        }
        self.params = params.to_vec();
        self.returns = returns;
        self.pure = pure;
        self.guarded_statements = self.compute_guarded_statements();
        Ok(())
    }
}
