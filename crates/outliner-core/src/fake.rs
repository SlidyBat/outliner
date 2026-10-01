//! A stand-in for Binary Ninja's MLIL and environment, so the matcher can be
//! tested headless: a fixture builder, an environment over reaching
//! definitions computed on the fake CFG, and a replay of rendered pattern text
//! (what *Show Function As Pattern Text* prints) as a fake function.

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;
use std::sync::Arc;

use crate::env::{Env, Merge, MergeSource};
use crate::il::{BlockSet, BranchKind, Builder, ExprId, Function, InstrSet, Operand, TypeId, VarId};
use crate::ops::Op;
use crate::pattern::{parse_function_text, Dest, Expr, PatternError, Stmt};

thread_local! {
    static TYPES: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

/// The fake type table: types are their printed text, interned per thread.
pub fn intern_type(text: &str) -> TypeId {
    TYPES.with(|t| {
        let mut t = t.borrow_mut();
        if let Some(i) = t.iter().position(|x| x == text) {
            return TypeId(i as u32);
        }
        t.push(text.to_string());
        TypeId(t.len() as u32 - 1)
    })
}

pub fn type_text(id: TypeId) -> String {
    TYPES.with(|t| t.borrow().get(id.0 as usize).cloned().unwrap_or_default())
}

// --------------------------------------------------------------------------- fixtures

/// Builds fake functions for the tests: expressions bottom-up,
/// then blocks of instruction roots with their successors.  Methods take
/// `&self` so that expressions nest (`fx.if_(fx.cmp(.., fx.v(s), fx.c(0)), 1, 3)`).
pub struct Fx {
    b: RefCell<Builder>,
}

impl Default for Fx {
    fn default() -> Self {
        Self::new()
    }
}

impl Fx {
    pub fn new() -> Fx {
        Fx { b: RefCell::new(Builder::new()) }
    }

    pub fn var(&self, name: &str) -> VarId {
        self.b.borrow_mut().named_var(name, None)
    }

    pub fn tvar(&self, name: &str, ty: &str) -> VarId {
        self.b.borrow_mut().named_var(name, Some(intern_type(ty)))
    }

    pub fn set_type(&self, v: VarId, ty: &str) {
        self.b.borrow_mut().set_var_type(v, Some(intern_type(ty)));
    }

    pub fn expr(&self, op: Op, size: u16, operands: &[Operand]) -> ExprId {
        self.b.borrow_mut().expr(op, size, operands)
    }

    pub fn set_expr_type(&self, e: ExprId, ty: &str) {
        self.b.borrow_mut().set_expr_type(e, Some(intern_type(ty)));
    }

    pub fn expr_size(&self, e: ExprId) -> u16 {
        self.b.borrow().expr_size(e)
    }

    // -- expressions --------------------------------------------------------
    pub fn v(&self, var: VarId) -> ExprId {
        self.vs(var, 8)
    }

    pub fn vs(&self, var: VarId, size: u16) -> ExprId {
        self.expr(Op::Var, size, &[Operand::Var(var)])
    }

    pub fn c(&self, n: i64) -> ExprId {
        self.cs(n, 8)
    }

    pub fn cs(&self, n: i64, size: u16) -> ExprId {
        self.expr(Op::Const, size, &[Operand::Int(n)])
    }

    pub fn cptr(&self, n: i64) -> ExprId {
        self.expr(Op::ConstPtr, 8, &[Operand::Int(n)])
    }

    pub fn load(&self, size: u16, addr: ExprId) -> ExprId {
        self.expr(Op::Load, size, &[Operand::Expr(addr)])
    }

    pub fn load_struct(&self, size: u16, src: ExprId, offset: i64) -> ExprId {
        self.expr(Op::LoadStruct, size, &[Operand::Expr(src), Operand::Int(offset)])
    }

    pub fn bin(&self, op: Op, a: ExprId, b: ExprId, size: u16) -> ExprId {
        self.expr(op, size, &[Operand::Expr(a), Operand::Expr(b)])
    }

    pub fn add(&self, a: ExprId, b: ExprId) -> ExprId {
        self.bin(Op::Add, a, b, 8)
    }

    pub fn sub(&self, a: ExprId, b: ExprId) -> ExprId {
        self.bin(Op::Sub, a, b, 8)
    }

    pub fn un(&self, op: Op, size: u16, e: ExprId) -> ExprId {
        self.expr(op, size, &[Operand::Expr(e)])
    }

    pub fn sx(&self, size: u16, e: ExprId) -> ExprId {
        self.un(Op::Sx, size, e)
    }

    pub fn zx(&self, size: u16, e: ExprId) -> ExprId {
        self.un(Op::Zx, size, e)
    }

    pub fn low_part(&self, size: u16, e: ExprId) -> ExprId {
        self.un(Op::LowPart, size, e)
    }

    /// A comparison at 8 bytes.
    pub fn cmp(&self, op: Op, a: ExprId, b: ExprId) -> ExprId {
        self.bin(op, a, b, 8)
    }

    pub fn and(&self, a: ExprId, b: ExprId, size: u16) -> ExprId {
        self.bin(Op::And, a, b, size)
    }

    pub fn address_of(&self, var: VarId) -> ExprId {
        self.expr(Op::AddressOf, 8, &[Operand::Var(var)])
    }

    pub fn var_field(&self, var: VarId, offset: i64, size: u16) -> ExprId {
        self.expr(Op::VarField, size, &[Operand::Var(var), Operand::Int(offset)])
    }

    // -- statements ----------------------------------------------------------
    pub fn set_var(&self, var: VarId, src: ExprId) -> ExprId {
        self.set_vars(var, src, 8)
    }

    pub fn set_vars(&self, var: VarId, src: ExprId, size: u16) -> ExprId {
        self.expr(Op::SetVar, size, &[Operand::Var(var), Operand::Expr(src)])
    }

    pub fn set_var_field(&self, var: VarId, offset: i64, src: ExprId, size: u16) -> ExprId {
        self.expr(Op::SetVarField, size, &[Operand::Var(var), Operand::Int(offset), Operand::Expr(src)])
    }

    pub fn store(&self, size: u16, dest: ExprId, src: ExprId) -> ExprId {
        self.expr(Op::Store, size, &[Operand::Expr(dest), Operand::Expr(src)])
    }

    pub fn if_(&self, cond: ExprId, t: u32, f: u32) -> ExprId {
        self.expr(Op::If, 0, &[Operand::Expr(cond), Operand::Int(t as i64), Operand::Int(f as i64)])
    }

    pub fn goto(&self, t: u32) -> ExprId {
        self.expr(Op::Goto, 0, &[Operand::Int(t as i64)])
    }

    pub fn ret(&self, values: &[ExprId]) -> ExprId {
        let items: Vec<Operand> = values.iter().map(|e| Operand::Expr(*e)).collect();
        let list = self.b.borrow_mut().list(&items);
        self.expr(Op::Ret, 0, &[list])
    }

    pub fn nop(&self) -> ExprId {
        self.expr(Op::Nop, 0, &[])
    }

    pub fn noret(&self) -> ExprId {
        self.expr(Op::Noret, 0, &[])
    }

    /// `outputs = call(dest, params)`; each output becomes an `MLIL_VAR_OUTPUT`.
    pub fn call(&self, outputs: &[VarId], dest: ExprId, params: &[ExprId]) -> ExprId {
        self.call_op(Op::Call, outputs, dest, params)
    }

    pub fn tailcall(&self, outputs: &[VarId], dest: ExprId, params: &[ExprId]) -> ExprId {
        self.call_op(Op::Tailcall, outputs, dest, params)
    }

    /// `outputs = intrinsic("name", params)`; the name gets an index of its own.
    pub fn intrinsic(&self, outputs: &[VarId], name: &str, params: &[ExprId]) -> ExprId {
        let index = self.b.borrow_mut().intern_intrinsic(name);
        let outs: Vec<Operand> = outputs.iter().map(|v| Operand::Var(*v)).collect();
        let outs = self.b.borrow_mut().list(&outs);
        let ps: Vec<Operand> = params.iter().map(|e| Operand::Expr(*e)).collect();
        let ps = self.b.borrow_mut().list(&ps);
        self.expr(Op::Intrinsic, 0, &[outs, Operand::Intrinsic(index), ps])
    }

    fn call_op(&self, op: Op, outputs: &[VarId], dest: ExprId, params: &[ExprId]) -> ExprId {
        let outs: Vec<Operand> = outputs.iter().map(|v| Operand::Expr(self.expr(Op::VarOutput, 0, &[Operand::Var(*v)]))).collect();
        let outs = self.b.borrow_mut().list(&outs);
        let ps: Vec<Operand> = params.iter().map(|e| Operand::Expr(*e)).collect();
        let ps = self.b.borrow_mut().list(&ps);
        self.expr(op, 0, &[outs, Operand::Expr(dest), ps])
    }

    /// Assemble the function from blocks of instruction roots and their
    /// successors (kind, block number).  The builder is emptied.
    pub fn func(&self, blocks: Vec<(Vec<ExprId>, Vec<(BranchKind, usize)>)>) -> Function {
        let mut b = std::mem::take(&mut *self.b.borrow_mut());
        let mut ids = Vec::new();
        for (instrs, _) in &blocks {
            let start = b.instr_count();
            for root in instrs {
                let index = b.instr_count();
                b.set_address(*root, 0x1000 + 4 * index as u64);
                b.instr(*root);
            }
            let end = b.instr_count();
            ids.push(b.block(start, end));
        }
        for (k, (_, succs)) in blocks.iter().enumerate() {
            for (kind, target) in succs {
                b.edge(*kind, ids[k], ids[*target]);
            }
        }
        b.finish()
    }
}

pub const U: BranchKind = BranchKind::Unconditional;
pub const T: BranchKind = BranchKind::True;
pub const FB: BranchKind = BranchKind::False;

// --------------------------------------------------------------------------- environment

/// Struct layouts by type name: (offset, size, member type text).
pub type Structs = HashMap<String, Vec<(i64, i64, String)>>;

struct Reaching {
    /// For every instruction, the definitions of each variable that reach its entry (-1: on entry to the function).
    before: Vec<HashMap<VarId, BTreeSet<i32>>>,
}

pub struct FakeEnv {
    symbols: HashMap<u64, Arc<[String]>>,
    pure: BTreeSet<u64>,
    /// address -> the bytes the binary holds there
    memory: Vec<(u64, Vec<u8>)>,
    structs: Structs,
    /// Typed globals: start, size in bytes, type.
    globals: Vec<(u64, u64, TypeId)>,
    reaching: RefCell<HashMap<usize, Rc<Reaching>>>,
}

impl Default for FakeEnv {
    fn default() -> Self {
        Self::new(HashMap::new(), BTreeSet::new(), Vec::new(), Structs::new())
    }
}

impl FakeEnv {
    pub fn new(symbols: HashMap<u64, Arc<[String]>>, pure: BTreeSet<u64>, memory: Vec<(u64, Vec<u8>)>, structs: Structs) -> FakeEnv {
        FakeEnv { symbols, pure, memory, structs, globals: Vec::new(), reaching: RefCell::new(HashMap::new()) }
    }

    /// Symbols from `(address, names)` pairs and pure addresses.
    pub fn with(symbols: &[(u64, &[&str])], pure: &[u64]) -> FakeEnv {
        let mut map = HashMap::new();
        for (addr, names) in symbols {
            map.insert(*addr, names.iter().map(|s| s.to_string()).collect::<Vec<_>>().into());
        }
        FakeEnv::new(map, pure.iter().copied().collect(), Vec::new(), Structs::new())
    }

    pub fn memory(mut self, memory: Vec<(u64, Vec<u8>)>) -> FakeEnv {
        self.memory = memory;
        self
    }

    pub fn structs(mut self, structs: Structs) -> FakeEnv {
        self.structs = structs;
        self
    }

    /// Typed globals as `(address, size, type)`: what the binary's data
    /// variables are.
    pub fn globals(mut self, globals: &[(u64, u64, &str)]) -> FakeEnv {
        self.globals = globals.iter().map(|(a, n, t)| (*a, *n, intern_type(t))).collect();
        self
    }

    fn reaching(&self, f: &Function) -> Rc<Reaching> {
        let key = f as *const Function as usize;
        if let Some(r) = self.reaching.borrow().get(&key) {
            return r.clone();
        }
        let r = Rc::new(compute_reaching(f));
        self.reaching.borrow_mut().insert(key, r.clone());
        r
    }

    fn reaching_defs(&self, f: &Function, use_index: u32, v: VarId) -> BTreeSet<i32> {
        self.reaching(f).before.get(use_index as usize).and_then(|m| m.get(&v)).cloned().unwrap_or_default()
    }

    /// Does the value of `v` on entry to `block` reach a read of `v` (on some
    /// path, before `v` is written again)?
    fn merged_value_is_read(&self, f: &Function, block: crate::il::BlockId, v: VarId) -> bool {
        let mut seen = f.block_set();
        let mut todo = vec![block];
        while let Some(cur) = todo.pop() {
            if seen.contains(cur.0 as usize) {
                continue;
            }
            seen.insert(cur.0 as usize);
            let mut killed = false;
            for i in f.block(cur).range() {
                let instr = f.instr(i);
                if f.vars_read(instr).contains(&v) {
                    return true;
                }
                if f.vars_written(instr).contains(&v) {
                    killed = true;
                    break;
                }
            }
            if !killed {
                todo.extend(f.block(cur).outgoing.iter().map(|e| e.target));
            }
        }
        false
    }
}

fn compute_reaching(f: &Function) -> Reaching {
    type Defs = HashMap<VarId, BTreeSet<i32>>;
    fn merge(dst: &mut Defs, src: &Defs) -> bool {
        let mut changed = false;
        for (var, defs) in src {
            let cur = dst.entry(*var).or_default();
            for d in defs {
                if cur.insert(*d) {
                    changed = true;
                }
            }
        }
        changed
    }
    let n = f.blocks.len();
    let mut block_in: Vec<Defs> = vec![Defs::new(); n];
    let mut block_out: Vec<Defs> = vec![Defs::new(); n];
    // Every variable starts with an "entry" pseudo-definition (-1): a parameter
    // or anything defined before the function, so a parameter merged with a
    // write in one arm is seen as a merge, like Binary Ninja's phi.
    let mut all_vars: BTreeSet<VarId> = BTreeSet::new();
    for i in 0..f.len() as u32 {
        all_vars.extend(f.vars_read(f.instr(i)));
        all_vars.extend(f.vars_written(f.instr(i)));
    }
    if n > 0 {
        for v in &all_vars {
            block_in[0].insert(*v, [-1].into_iter().collect());
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for b in &f.blocks {
            let id = b.id.0 as usize;
            let mut inc = Defs::new();
            for e in &b.incoming {
                merge(&mut inc, &block_out[e.source.0 as usize]);
            }
            if merge(&mut block_in[id], &inc) {
                changed = true;
            }
            let mut out = block_in[id].clone();
            for i in b.range() {
                for v in f.vars_written(f.instr(i)) {
                    out.insert(v, [i as i32].into_iter().collect());
                }
            }
            if out != block_out[id] {
                block_out[id] = out;
                changed = true;
            }
        }
    }
    let mut before: Vec<Defs> = vec![Defs::new(); f.len()];
    for b in &f.blocks {
        let mut cur = block_in[b.id.0 as usize].clone();
        for i in b.range() {
            before[i as usize] = cur.clone();
            for v in f.vars_written(f.instr(i)) {
                cur.insert(v, [i as i32].into_iter().collect());
            }
        }
    }
    Reaching { before }
}

fn normalize_type(text: &str) -> String {
    // `const` is dropped on word boundaries, so `Entry const*` loses it as
    // readily as `const Entry *` does.
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(pos) = rest.find("const") {
        let (before, after) = (&rest[..pos], &rest[pos + 5..]);
        let starts_word = before.chars().next_back().is_none_or(|c| !(c.is_alphanumeric() || c == '_'));
        let ends_word = after.chars().next().is_none_or(|c| !(c.is_alphanumeric() || c == '_'));
        out.push_str(before);
        if !(starts_word && ends_word) {
            out.push_str("const");
        } else {
            out.push(' ');
        }
        rest = after;
    }
    out.push_str(rest);
    let words: Vec<&str> = out.split_whitespace().collect();
    words.join(" ").replace(" *", "*").replace(" &", "&")
}

impl Env for FakeEnv {
    fn type_of_expr(&self, f: &Function, e: ExprId) -> Option<TypeId> {
        if f.op(e) == Op::Var {
            return f.var_of(e).and_then(|v| f.var(v).ty);
        }
        f.expr(e).ty
    }

    fn type_of_var(&self, f: &Function, v: VarId) -> Option<TypeId> {
        f.var(v).ty
    }

    fn pointer_to(&self, t: TypeId) -> Option<TypeId> {
        Some(intern_type(&format!("{}*", type_text(t))))
    }

    fn types_match(&self, actual: TypeId, constraint: &crate::pattern::TypeConstraint) -> bool {
        let text = type_text(actual);
        if constraint.is_regex() {
            return constraint.regex_matches(&text);
        }
        let strip = |s: &str| s.split_whitespace().collect::<String>();
        strip(&text) == strip(&constraint.text)
    }

    fn type_text(&self, t: TypeId) -> String {
        type_text(t)
    }

    fn symbol_names_at(&self, addr: u64) -> Arc<[String]> {
        self.symbols.get(&addr).cloned().unwrap_or_else(|| Vec::new().into())
    }

    fn definition_of(&self, f: &Function, use_index: u32, var: VarId) -> Option<u32> {
        let defs = self.reaching_defs(f, use_index, var);
        if defs.len() != 1 {
            return None;
        }
        let d = *defs.iter().next().unwrap();
        if d < 0 {
            return None;
        }
        let d = d as u32;
        let instr = f.instr(d);
        match f.op(instr) {
            Op::SetVar | Op::SetVarField => Some(d),
            Op::Call if f.call_outputs(instr).as_slice() == [var] => Some(d),
            _ => None,
        }
    }

    fn uses_of(&self, f: &Function, def_index: u32, var: VarId, kept_blocks: Option<&BlockSet>) -> Vec<u32> {
        let mut out = Vec::new();
        for u in 0..f.len() as u32 {
            if !f.vars_read(f.instr(u)).contains(&var) {
                continue;
            }
            let reaching = self.reaching_defs(f, u, var);
            if !reaching.contains(&(def_index as i32)) {
                continue;
            }
            if let Some(kept) = kept_blocks {
                let def_kept = kept.contains(f.block_id_of(def_index).0 as usize);
                let other_kept = reaching
                    .iter()
                    .any(|d| *d >= 0 && *d != def_index as i32 && kept.contains(f.block_id_of(*d as u32).0 as usize));
                if !def_kept && other_kept {
                    continue; // on the kept path the value comes from the other definition
                }
            }
            out.push(u);
        }
        out
    }

    fn merges_of(&self, f: &Function, def_index: u32, var: VarId, at_index: u32) -> Option<Vec<Merge>> {
        // Every block with several predecessors whose entry sees this definition
        // next to others is a merge (Binary Ninja would place a phi there); it
        // counts when the merged value can still be read.
        let live = self.reaching_defs(f, at_index, var);
        let mut out = Vec::new();
        for b in &f.blocks {
            if b.incoming.len() < 2 {
                continue;
            }
            let reaching = self.reaching_defs(f, b.start, var);
            if !reaching.contains(&(def_index as i32)) || reaching.len() < 2 {
                continue;
            }
            if !self.merged_value_is_read(f, b.id, var) {
                continue;
            }
            let mut others = Vec::new();
            for d in &reaching {
                if *d == def_index as i32 {
                    continue;
                }
                if live.len() == 1 && live.contains(d) {
                    others.push(MergeSource::Live);
                } else if *d >= 0 {
                    others.push(MergeSource::Def(*d as u32));
                } else {
                    others.push(MergeSource::Unknown);
                }
            }
            out.push(Merge { block_start: b.start, others });
        }
        Some(out)
    }

    fn uses_outside(&self, f: &Function, instr_index: u32, region: &InstrSet, var: VarId) -> bool {
        self.uses_of(f, instr_index, var, None).iter().any(|u| !region.contains(*u as usize))
    }

    fn read_bytes(&self, addr: u64, size: usize) -> Option<Vec<u8>> {
        for (start, raw) in &self.memory {
            if *start <= addr && addr + size as u64 <= *start + raw.len() as u64 {
                let off = (addr - start) as usize;
                return Some(raw[off..off + size].to_vec());
            }
        }
        None
    }

    fn find_bytes(&self, data: &[u8]) -> Option<u64> {
        for (start, raw) in &self.memory {
            if let Some(k) = raw.windows(data.len()).position(|w| w == data) {
                return Some(start + k as u64);
            }
        }
        None
    }

    fn member_containing(&self, t: TypeId, offset: i64, deref: bool) -> Option<(i64, TypeId)> {
        let mut text = normalize_type(&type_text(t));
        if deref {
            if !(text.ends_with('*') || text.ends_with('&')) {
                return None;
            }
            text.pop();
            text = text.trim().to_string();
        }
        let members = self.structs.get(&text).or_else(|| self.structs.get(text.strip_prefix("struct ").unwrap_or(&text)))?;
        for (off, size, mtype) in members {
            if *off <= offset && offset < off + size {
                return Some((*off, intern_type(mtype)));
            }
        }
        None
    }

    fn data_var_containing(&self, addr: u64) -> Option<(u64, TypeId)> {
        self.globals.iter().find(|(start, size, _)| *start <= addr && addr < start + size).map(|(start, _, t)| (*start, *t))
    }

    fn is_pure_call(&self, f: &Function, instr: u32) -> bool {
        let e = f.instr(instr);
        match f.call_dest(e) {
            Some(d) if f.op(d) == Op::ConstPtr => f.int_operand(d, 0).map(|a| self.pure.contains(&(a as u64))).unwrap_or(false),
            _ => false,
        }
    }
}

// --------------------------------------------------------------------------- rendered functions as fakes

pub const PURE_NAMES: [&str; 9] = [
    "std::string::size",
    "std::string::data",
    "std::string::empty",
    "std::string::front",
    "std::string::back",
    "std::string::capacity",
    "std::string::find",
    "std::string::rfind",
    "std::string::compare",
];

/// A fake function replayed from pattern text: the function, its variables by
/// name, and the addresses the call targets were given.
pub struct Loaded {
    pub func: Function,
    pub vars: HashMap<String, VarId>,
    pub addresses: HashMap<String, u64>,
}

impl Loaded {
    pub fn var(&self, name: &str) -> VarId {
        *self.vars.get(name).unwrap_or_else(|| panic!("no variable {name}"))
    }

    pub fn addr(&self, name: &str) -> u64 {
        self.addresses[name]
    }

    /// A FakeEnv for the function; `aliases` gives call targets their other names.
    pub fn env(&self, pure: &[&str], memory: Vec<(u64, Vec<u8>)>, structs: Structs, aliases: &[(&str, &[&str])]) -> FakeEnv {
        let mut symbols: HashMap<u64, Arc<[String]>> = HashMap::new();
        let mut pure_addrs = BTreeSet::new();
        for (name, addr) in &self.addresses {
            let mut names = vec![name.clone()];
            for (n, extra) in aliases {
                if n == name {
                    names.extend(extra.iter().map(|s| s.to_string()));
                }
            }
            symbols.insert(*addr, names.into());
            if pure.contains(&name.as_str()) {
                pure_addrs.insert(*addr);
            }
        }
        FakeEnv::new(symbols, pure_addrs, memory, structs)
    }
}

fn var_positions(op: Op) -> &'static [usize] {
    match op {
        Op::Var | Op::VarField | Op::SetVar | Op::SetVarField | Op::AddressOf | Op::AddressOfField => &[0],
        Op::VarSplit | Op::SetVarSplit => &[0, 1],
        _ => &[],
    }
}

fn int_positions(op: Op) -> &'static [usize] {
    match op {
        Op::LoadStruct | Op::StoreStruct | Op::VarField | Op::SetVarField | Op::AddressOfField => &[1],
        Op::Const | Op::ConstPtr | Op::ConstData => &[0],
        _ => &[],
    }
}

fn const_int(e: &Expr) -> Result<i64, PatternError> {
    match e {
        Expr::Const(c) => Ok(*c as i64),
        Expr::Op(o) if o.op == Op::Neg && o.args.len() == 1 => match &o.args[0] {
            Expr::Const(c) => Ok(-(*c as i64)),
            _ => Err(PatternError(format!("an integer operand was expected, not {e:?}"))),
        },
        Expr::Wildcard => Ok(0),
        _ => Err(PatternError(format!("an integer operand was expected, not {e:?}"))),
    }
}

/// Build a fake function from rendered pattern text.  `types` gives variables
/// their types (parameters and typed locals); sizes come from the size suffixes
/// in the text and from the assignments that define variables.  Call targets
/// named in the text get distinct addresses.
pub fn from_pattern_text(text: &str, types: &[(&str, &str)]) -> Result<Loaded, PatternError> {
    let pattern = parse_function_text(text)?;
    let fx = Fx::new();
    let mut vars: HashMap<String, VarId> = HashMap::new();
    let mut addresses: HashMap<String, u64> = HashMap::new();
    let mut var_sizes: HashMap<String, u16> = HashMap::new();

    struct Ctx<'p> {
        pattern: &'p crate::pattern::Pattern,
        starts: HashMap<Option<crate::pattern::LabelId>, u32>,
    }
    let mut starts = HashMap::new();
    let mut count = 0u32;
    for b in &pattern.blocks {
        starts.insert(b.label, count);
        count += b.stmts.len() as u32;
    }
    let ctx = Ctx { pattern: &pattern, starts };

    fn v(fx: &Fx, vars: &mut HashMap<String, VarId>, types: &[(&str, &str)], name: &str) -> VarId {
        if let Some(id) = vars.get(name) {
            return *id;
        }
        let id = match types.iter().find(|(n, _)| *n == name) {
            Some((_, t)) => fx.tvar(name, t),
            None => fx.var(name),
        };
        vars.insert(name.to_string(), id);
        id
    }
    fn a(addresses: &mut HashMap<String, u64>, name: &str) -> u64 {
        if let Some(x) = addresses.get(name) {
            return *x;
        }
        let x = 0x7000 + 0x10 * addresses.len() as u64;
        addresses.insert(name.to_string(), x);
        x
    }

    #[allow(clippy::too_many_arguments)]
    fn e(
        fx: &Fx,
        ctx: &Ctx,
        vars: &mut HashMap<String, VarId>,
        addresses: &mut HashMap<String, u64>,
        var_sizes: &HashMap<String, u16>,
        types: &[(&str, &str)],
        expr: &Expr,
        hint: u16,
    ) -> Result<ExprId, PatternError> {
        match expr {
            Expr::Placeholder(p) => {
                let name = ctx.pattern.ph_name(*p);
                let id = v(fx, vars, types, name);
                let size = var_sizes.get(name).copied().unwrap_or(hint);
                Ok(fx.vs(id, size))
            }
            Expr::Const(c) => Ok(fx.cs(*c as i64, hint)),
            Expr::Wildcard => Ok(fx.cs(0, hint)),
            Expr::Symbol(s) => {
                let addr = a(addresses, &s.name);
                Ok(fx.cptr(addr as i64))
            }
            Expr::Call(_) => Err(PatternError("a call inside an expression cannot be replayed".into())),
            Expr::Op(o) => {
                if o.op == Op::Neg && o.args.len() == 1 {
                    if let Expr::Const(c) = o.args[0] {
                        return Ok(fx.cs(-(c as i64), hint));
                    }
                }
                let size = match o.size {
                    Some(s) => s,
                    None => {
                        // unsized in the text: a binary operation takes its operands' size,
                        // a comparison its operands', a load its hint
                        let known = o
                            .args
                            .iter()
                            .filter(|x| !matches!(x, Expr::Const(_) | Expr::Wildcard))
                            .filter_map(|x| match x {
                                Expr::Placeholder(p) => var_sizes.get(ctx.pattern.ph_name(*p)).copied(),
                                Expr::Op(inner) => inner.size,
                                _ => None,
                            })
                            .find(|s| *s != 0);
                        known.unwrap_or(hint)
                    }
                };
                let mut operands = Vec::new();
                for (k, arg) in o.args.iter().enumerate() {
                    if var_positions(o.op).contains(&k) {
                        let Expr::Placeholder(p) = arg else {
                            return Err(PatternError(format!("a variable operand was expected, not {arg:?}")));
                        };
                        let name = ctx.pattern.ph_name(*p);
                        operands.push(Operand::Var(v(fx, vars, types, name)));
                    } else if int_positions(o.op).contains(&k) {
                        operands.push(Operand::Int(const_int(arg)?));
                    } else {
                        operands.push(Operand::Expr(e(fx, ctx, vars, addresses, var_sizes, types, arg, size)?));
                    }
                }
                Ok(fx.expr(o.op, size, &operands))
            }
        }
    }

    let mut blocks: Vec<(Vec<ExprId>, Vec<(BranchKind, usize)>)> = Vec::new();
    let mut block_no: HashMap<Option<crate::pattern::LabelId>, usize> = HashMap::new();
    for (k, b) in pattern.blocks.iter().enumerate() {
        block_no.insert(b.label, k);
    }
    for (k, b) in pattern.blocks.iter().enumerate() {
        let mut instrs = Vec::new();
        for stmt in &b.stmts {
            let root = match stmt {
                Stmt::SetVar { dest, src } => {
                    let src_e = e(&fx, &ctx, &mut vars, &mut addresses, &var_sizes, types, src, 8)?;
                    let size = match fx.expr_size(src_e) {
                        0 => 8,
                        s => s,
                    };
                    match dest {
                        Dest::Ph(p) => {
                            let name = pattern.ph_name(*p).to_string();
                            var_sizes.insert(name.clone(), size);
                            let id = v(&fx, &mut vars, types, &name);
                            fx.set_vars(id, src_e, size)
                        }
                        Dest::Wildcard => {
                            let id = v(&fx, &mut vars, types, "_");
                            fx.set_vars(id, src_e, size)
                        }
                    }
                }
                Stmt::Store { size, dest, src } => {
                    let src_e = e(&fx, &ctx, &mut vars, &mut addresses, &var_sizes, types, src, size.unwrap_or(8))?;
                    let dest_e = e(&fx, &ctx, &mut vars, &mut addresses, &var_sizes, types, dest, 8)?;
                    let s = size.unwrap_or_else(|| fx.expr_size(src_e));
                    fx.store(s, dest_e, src_e)
                }
                Stmt::Call(c) => {
                    let outputs: Vec<VarId> = c
                        .outputs
                        .iter()
                        .map(|o| match o {
                            Dest::Ph(p) => v(&fx, &mut vars, types, pattern.ph_name(*p)),
                            Dest::Wildcard => v(&fx, &mut vars, types, "_"),
                        })
                        .collect();
                    let dest = match &c.target {
                        Expr::Symbol(s) => {
                            let addr = a(&mut addresses, &s.name);
                            fx.cptr(addr as i64)
                        }
                        other => e(&fx, &ctx, &mut vars, &mut addresses, &var_sizes, types, other, 8)?,
                    };
                    let mut params = Vec::new();
                    for arg in &c.args {
                        params.push(e(&fx, &ctx, &mut vars, &mut addresses, &var_sizes, types, arg, 8)?);
                    }
                    fx.call(&outputs, dest, &params)
                }
                Stmt::Intrinsic(c) => {
                    let outputs: Vec<VarId> = c
                        .outputs
                        .iter()
                        .map(|o| match o {
                            Dest::Ph(p) => v(&fx, &mut vars, types, pattern.ph_name(*p)),
                            Dest::Wildcard => v(&fx, &mut vars, types, "_"),
                        })
                        .collect();
                    let mut params = Vec::new();
                    for arg in &c.args {
                        params.push(e(&fx, &ctx, &mut vars, &mut addresses, &var_sizes, types, arg, 8)?);
                    }
                    fx.intrinsic(&outputs, &c.name.name, &params)
                }
                Stmt::Ret(values) => {
                    let mut vs = Vec::new();
                    for val in values {
                        match val {
                            Expr::Call(c) => {
                                // `return call(...)`: a tail call
                                let dest = match &c.target {
                                    Expr::Symbol(s) => {
                                        let addr = a(&mut addresses, &s.name);
                                        fx.cptr(addr as i64)
                                    }
                                    other => e(&fx, &ctx, &mut vars, &mut addresses, &var_sizes, types, other, 8)?,
                                };
                                let mut params = Vec::new();
                                for arg in &c.args {
                                    params.push(e(&fx, &ctx, &mut vars, &mut addresses, &var_sizes, types, arg, 8)?);
                                }
                                vs.clear();
                                let root = fx.tailcall(&[], dest, &params);
                                instrs.push(root);
                                continue;
                            }
                            other => vs.push(e(&fx, &ctx, &mut vars, &mut addresses, &var_sizes, types, other, 8)?),
                        }
                    }
                    if values.len() == 1 && matches!(values[0], Expr::Call(_)) {
                        continue;
                    }
                    fx.ret(&vs)
                }
                Stmt::Nop => fx.nop(),
                Stmt::If { cond, t, f } => {
                    let c = e(&fx, &ctx, &mut vars, &mut addresses, &var_sizes, types, cond, 8)?;
                    let ts = *ctx.starts.get(&Some(*t)).ok_or_else(|| PatternError("if target has no block".into()))?;
                    let fs = *ctx.starts.get(&Some(*f)).ok_or_else(|| PatternError("if target has no block".into()))?;
                    fx.if_(c, ts, fs)
                }
                Stmt::Goto(l) => {
                    let ts = *ctx.starts.get(&Some(*l)).ok_or_else(|| PatternError("goto target has no block".into()))?;
                    fx.goto(ts)
                }
                Stmt::Expr(x) => e(&fx, &ctx, &mut vars, &mut addresses, &var_sizes, types, x, 8)?,
            };
            instrs.push(root);
        }
        let succs: Vec<(BranchKind, usize)> = match b.stmts.last() {
            Some(Stmt::If { t, f, .. }) => vec![(T, block_no[&Some(*t)]), (FB, block_no[&Some(*f)])],
            Some(Stmt::Goto(l)) => vec![(U, block_no[&Some(*l)])],
            Some(Stmt::Ret(_)) => vec![],
            Some(Stmt::Expr(Expr::Op(o))) if o.op == Op::Noret => vec![],
            _ => {
                if k + 1 < pattern.blocks.len() {
                    vec![(BranchKind::FallThrough, k + 1)]
                } else {
                    vec![]
                }
            }
        };
        blocks.push((instrs, succs));
    }
    Ok(Loaded { func: fx.func(blocks), vars, addresses })
}
