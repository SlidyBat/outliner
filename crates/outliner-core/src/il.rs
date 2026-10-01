//! A snapshot of one MLIL function: the tree of every instruction, the
//! variables and the basic blocks, in flat arenas.
//!
//! The matcher revisits instructions and their operand trees constantly, so
//! the host reads the function once into this structure and the matcher never
//! calls back into it for the IL itself.  A snapshot lives for one matching
//! round and is dropped with it.  It has no Binary Ninja dependency: the unit
//! tests build snapshots by hand and from rendered pattern text.

use std::fmt;

use fixedbitset::FixedBitSet;
use smallvec::SmallVec;

use crate::ops::{Op, OperandKind};

/// Index of an expression in [`Function::exprs`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExprId(pub u32);

/// Index of a variable in [`Function::vars`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VarId(pub u32);

/// Index of a basic block in [`Function::blocks`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BlockId(pub u32);

/// A type as the host's environment knows it; opaque to the matcher.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeId(pub u32);

/// A set of instruction indices.
pub type InstrSet = FixedBitSet;
/// A set of basic blocks by [`BlockId`].
pub type BlockSet = FixedBitSet;

/// One raw operand of an expression.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Operand {
    Expr(ExprId),
    Var(VarId),
    Int(i64),
    /// A floating point constant, as its raw bits.
    Float(u64),
    Intrinsic(u32),
    /// A list of operands in [`Function::lists`].
    List { start: u32, len: u32 },
    /// `MLIL_CONST_DATA`: the register value state and the value.
    ConstData { state: u32, value: i64 },
    /// An `MLIL_ASSERT` constraint: an index into the host's cached value sets.
    Constraint(u64),
    /// Anything the snapshot does not interpret (an SSA version, for instance).
    Raw(u64),
}

/// An expression or instruction of the function.
#[derive(Clone, Debug)]
pub struct Expr {
    pub op: Op,
    pub size: u16,
    /// The expression's index in the host's IL function (the fake gives each a distinct one).
    pub source: u32,
    /// The instruction the expression belongs to.
    pub instr: u32,
    pub address: u64,
    pub source_operand: u32,
    /// The expression's type, when the host recorded it (the fakes do; Binary Ninja answers lazily).
    pub ty: Option<TypeId>,
    operands: u32,
    operand_count: u8,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum BranchKind {
    Unconditional,
    FallThrough,
    True,
    False,
    Other,
}

impl BranchKind {
    pub fn is_unconditional(self) -> bool {
        matches!(self, BranchKind::Unconditional | BranchKind::FallThrough)
    }

    pub fn from_name(name: &str) -> BranchKind {
        match name {
            "UnconditionalBranch" => BranchKind::Unconditional,
            "FallThrough" => BranchKind::FallThrough,
            "TrueBranch" => BranchKind::True,
            "FalseBranch" => BranchKind::False,
            _ => BranchKind::Other,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            BranchKind::Unconditional => "UnconditionalBranch",
            BranchKind::FallThrough => "FallThrough",
            BranchKind::True => "TrueBranch",
            BranchKind::False => "FalseBranch",
            BranchKind::Other => "OtherBranch",
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Edge {
    pub kind: BranchKind,
    pub source: BlockId,
    pub target: BlockId,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub id: BlockId,
    /// First instruction index.
    pub start: u32,
    /// One past the last instruction index.
    pub end: u32,
    pub outgoing: Vec<Edge>,
    pub incoming: Vec<Edge>,
}

impl Block {
    pub fn range(&self) -> std::ops::Range<u32> {
        self.start..self.end
    }

    pub fn contains(&self, index: u32) -> bool {
        self.start <= index && index < self.end
    }
}

/// A variable of the function: the host's identity plus its display name.
#[derive(Clone, Debug)]
pub struct VarInfo {
    pub source_type: u32,
    pub index: u32,
    pub storage: i64,
    pub name: String,
    pub ty: Option<TypeId>,
}

/// The snapshot.
#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub start: u64,
    pub address_size: u8,
    pub exprs: Vec<Expr>,
    operands: Vec<Operand>,
    lists: Vec<Operand>,
    /// Root expression of each instruction.
    pub instrs: Vec<ExprId>,
    pub blocks: Vec<Block>,
    block_of: Vec<BlockId>,
    pub vars: Vec<VarInfo>,
    /// The names of the intrinsics the function uses, by the host's index.
    intrinsics: Vec<(u32, String)>,
}

impl Function {
    pub fn builder() -> Builder {
        Builder::new()
    }

    /// Number of instructions.
    pub fn len(&self) -> usize {
        self.instrs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.instrs.is_empty()
    }

    /// The root expression of instruction `index`.
    pub fn instr(&self, index: u32) -> ExprId {
        self.instrs[index as usize]
    }

    pub fn expr(&self, id: ExprId) -> &Expr {
        &self.exprs[id.0 as usize]
    }

    pub fn op(&self, id: ExprId) -> Op {
        self.exprs[id.0 as usize].op
    }

    pub fn instr_op(&self, index: u32) -> Op {
        self.op(self.instr(index))
    }

    pub fn size(&self, id: ExprId) -> u16 {
        self.exprs[id.0 as usize].size
    }

    pub fn operands(&self, id: ExprId) -> &[Operand] {
        let e = &self.exprs[id.0 as usize];
        &self.operands[e.operands as usize..e.operands as usize + e.operand_count as usize]
    }

    pub fn operand(&self, id: ExprId, k: usize) -> Operand {
        self.operands(id)[k]
    }

    /// The items of a list operand.
    pub fn list(&self, operand: Operand) -> &[Operand] {
        match operand {
            Operand::List { start, len } => &self.lists[start as usize..(start + len) as usize],
            _ => &[],
        }
    }

    /// The expression a sub-expression operand denotes, if it is one.
    pub fn sub(&self, id: ExprId, k: usize) -> Option<ExprId> {
        match self.operands(id).get(k) {
            Some(Operand::Expr(e)) => Some(*e),
            _ => None,
        }
    }

    pub fn var_operand(&self, id: ExprId, k: usize) -> Option<VarId> {
        match self.operands(id).get(k) {
            Some(Operand::Var(v)) => Some(*v),
            _ => None,
        }
    }

    pub fn int_operand(&self, id: ExprId, k: usize) -> Option<i64> {
        match self.operands(id).get(k) {
            Some(Operand::Int(v)) => Some(*v),
            _ => None,
        }
    }

    /// The variable an `MLIL_VAR` expression reads.
    pub fn var_of(&self, id: ExprId) -> Option<VarId> {
        if self.op(id) == Op::Var {
            self.var_operand(id, 0)
        } else {
            None
        }
    }

    /// The value of a constant expression (`MLIL_CONST`, `MLIL_CONST_PTR`).
    pub fn const_value(&self, id: ExprId) -> Option<i64> {
        if self.op(id).is_const_op() {
            self.int_operand(id, 0)
        } else {
            None
        }
    }

    /// The instruction index of an expression.
    /// The name of an intrinsic, when the host recorded it.
    pub fn intrinsic_name(&self, index: u32) -> Option<&str> {
        self.intrinsics.iter().find(|(i, _)| *i == index).map(|(_, n)| n.as_str())
    }

    pub fn instr_of(&self, id: ExprId) -> u32 {
        self.exprs[id.0 as usize].instr
    }

    pub fn block_of(&self, index: u32) -> &Block {
        &self.blocks[self.block_of[index as usize].0 as usize]
    }

    pub fn block_id_of(&self, index: u32) -> BlockId {
        self.block_of[index as usize]
    }

    pub fn block(&self, id: BlockId) -> &Block {
        &self.blocks[id.0 as usize]
    }

    /// The block starting at instruction `start`, if any.
    pub fn block_at(&self, start: u32) -> Option<&Block> {
        if (start as usize) < self.instrs.len() {
            let b = self.block_of(start);
            if b.start == start {
                return Some(b);
            }
        }
        None
    }

    pub fn var(&self, id: VarId) -> &VarInfo {
        &self.vars[id.0 as usize]
    }

    pub fn var_name(&self, id: VarId) -> &str {
        &self.vars[id.0 as usize].name
    }

    pub fn instr_set(&self) -> InstrSet {
        InstrSet::with_capacity(self.len())
    }

    pub fn block_set(&self) -> BlockSet {
        BlockSet::with_capacity(self.blocks.len())
    }

    /// The targets of an `MLIL_IF` instruction.
    pub fn if_targets(&self, id: ExprId) -> Option<(u32, u32)> {
        if self.op(id) != Op::If {
            return None;
        }
        Some((self.int_operand(id, 1)? as u32, self.int_operand(id, 2)? as u32))
    }

    pub fn goto_target(&self, id: ExprId) -> Option<u32> {
        if self.op(id) != Op::Goto {
            return None;
        }
        self.int_operand(id, 0).map(|t| t as u32)
    }

    // -- calls ------------------------------------------------------------------

    /// The output variables of a call (the `dest` of each `MLIL_VAR_OUTPUT`).
    pub fn call_outputs(&self, id: ExprId) -> SmallVec<[VarId; 2]> {
        let mut out = SmallVec::new();
        if !self.op(id).is_call_like() {
            return out;
        }
        for item in self.list(self.operand(id, 0)) {
            if let Operand::Expr(e) = item {
                // A by-reference output wraps the output node it writes through.
                let mut e = *e;
                while self.op(e) == Op::ReturnByRef {
                    match self.sub(e, 0) {
                        Some(inner) => e = inner,
                        None => break,
                    }
                }
                if let Some(v) = self.var_operand(e, 0) {
                    out.push(v);
                }
            }
        }
        out
    }

    /// The destination expression of a call.
    pub fn call_dest(&self, id: ExprId) -> Option<ExprId> {
        match self.op(id) {
            Op::Call | Op::CallUntyped | Op::Tailcall | Op::TailcallUntyped => self.sub(id, 1),
            _ => None,
        }
    }

    /// The parameter expressions of a call.
    pub fn call_params(&self, id: ExprId) -> SmallVec<[ExprId; 6]> {
        let mut out = SmallVec::new();
        let list = match self.op(id) {
            Op::Call | Op::Tailcall => self.operand(id, 2),
            Op::Syscall => self.operand(id, 1),
            Op::CallUntyped | Op::TailcallUntyped => match self.sub(id, 2) {
                Some(p) => self.operand(p, 0),
                None => return out,
            },
            Op::SyscallUntyped => match self.sub(id, 1) {
                Some(p) => self.operand(p, 0),
                None => return out,
            },
            _ => return out,
        };
        for item in self.list(list) {
            if let Operand::Expr(e) = item {
                out.push(*e);
            }
        }
        out
    }

    // -- variables read and written ---------------------------------------------

    /// Variables an instruction writes.
    pub fn vars_written(&self, id: ExprId) -> SmallVec<[VarId; 2]> {
        let mut out = SmallVec::new();
        match self.op(id) {
            Op::SetVar | Op::SetVarField => out.extend(self.var_operand(id, 0)),
            Op::SetVarSplit => {
                out.extend(self.var_operand(id, 0));
                out.extend(self.var_operand(id, 1));
            }
            Op::Intrinsic => {
                for item in self.list(self.operand(id, 0)) {
                    if let Operand::Var(v) = item {
                        out.push(*v);
                    }
                }
            }
            op if op.is_call_like() => out = self.call_outputs(id),
            _ => {}
        }
        out
    }

    /// Variables an instruction or expression reads.
    pub fn vars_read(&self, id: ExprId) -> SmallVec<[VarId; 4]> {
        let mut out = SmallVec::new();
        self.collect_reads(id, &mut out);
        out
    }

    fn collect_reads(&self, id: ExprId, out: &mut SmallVec<[VarId; 4]>) {
        match self.op(id) {
            Op::SetVar => {
                if let Some(src) = self.sub(id, 1) {
                    self.collect_reads(src, out);
                }
            }
            Op::Intrinsic => {
                for item in self.list(self.operand(id, 2)) {
                    if let Operand::Expr(e) = item {
                        self.collect_reads(*e, out);
                    }
                }
            }
            op if op.is_call_like() => {
                if let Some(dest) = self.call_dest(id) {
                    self.collect_reads(dest, out);
                }
                for p in self.call_params(id) {
                    self.collect_reads(p, out);
                }
            }
            _ => {
                for operand in self.operands(id) {
                    self.collect_operand_reads(*operand, out);
                }
            }
        }
    }

    fn collect_operand_reads(&self, operand: Operand, out: &mut SmallVec<[VarId; 4]>) {
        match operand {
            Operand::Var(v) => out.push(v),
            Operand::Expr(e) => self.collect_reads(e, out),
            Operand::List { .. } => {
                for item in self.list(operand) {
                    self.collect_operand_reads(*item, out);
                }
            }
            _ => {}
        }
    }

    // -- trees --------------------------------------------------------------------

    /// Whether evaluating `id` reads or writes memory, or has another effect
    /// (a call, a store, an intrinsic): what may not move across a store.
    pub fn touches_memory(&self, id: ExprId) -> bool {
        let touches = |e: ExprId| {
            let op = self.op(e);
            op.is_impure() || matches!(op, Op::Load | Op::LoadStruct | Op::LoadSsa | Op::LoadStructSsa)
        };
        if touches(id) {
            return true;
        }
        let mut subs = Vec::new();
        self.subexprs(id, &mut subs);
        subs.into_iter().any(touches)
    }

    /// Every sub-expression of `id` in pre-order, `id` itself excluded.
    pub fn subexprs(&self, id: ExprId, out: &mut Vec<ExprId>) {
        for operand in self.operands(id) {
            self.subexprs_of_operand(*operand, out);
        }
    }

    fn subexprs_of_operand(&self, operand: Operand, out: &mut Vec<ExprId>) {
        match operand {
            Operand::Expr(e) => {
                out.push(e);
                self.subexprs(e, out);
            }
            Operand::List { .. } => {
                for item in self.list(operand) {
                    self.subexprs_of_operand(*item, out);
                }
            }
            _ => {}
        }
    }

    /// `id` and every sub-expression of it.
    pub fn subtree(&self, id: ExprId) -> Vec<ExprId> {
        let mut out = vec![id];
        self.subexprs(id, &mut out);
        out
    }

    /// Structural equality of two expression trees.  With `ignore_size` (used for
    /// address expressions) operation widths do not count.
    pub fn expr_equal(&self, a: ExprId, b: ExprId, ignore_size: bool) -> bool {
        if a == b {
            return true;
        }
        let (ea, eb) = (self.expr(a), self.expr(b));
        if ea.op != eb.op || (!ignore_size && ea.size != eb.size) {
            return false;
        }
        let (oa, ob) = (self.operands(a), self.operands(b));
        if oa.len() != ob.len() {
            return false;
        }
        for (k, (x, y)) in oa.iter().zip(ob).enumerate() {
            if !self.operand_equal(*x, *y, ignore_size || ea.op.is_address_operand(k)) {
                return false;
            }
        }
        true
    }

    fn operand_equal(&self, x: Operand, y: Operand, ignore_size: bool) -> bool {
        match (x, y) {
            (Operand::Expr(p), Operand::Expr(q)) => self.expr_equal(p, q, ignore_size),
            (Operand::List { .. }, Operand::List { .. }) => {
                let (lx, ly) = (self.list(x), self.list(y));
                lx.len() == ly.len() && lx.iter().zip(ly).all(|(p, q)| self.operand_equal(*p, *q, false))
            }
            (Operand::Expr(_), _) | (_, Operand::Expr(_)) => false,
            _ => x == y,
        }
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<function {} @ {:#x}, {} instructions>", self.name, self.start, self.len())
    }
}

/// Builds a [`Function`] bottom-up: create expressions, then instructions from
/// their roots, then blocks and edges.
pub struct Builder {
    f: Function,
    var_index: std::collections::HashMap<(u32, u32, i64), VarId>,
    next_source: u32,
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

impl Builder {
    pub fn new() -> Self {
        Builder {
            f: Function {
                name: String::new(),
                start: 0,
                address_size: 8,
                exprs: Vec::new(),
                operands: Vec::new(),
                lists: Vec::new(),
                instrs: Vec::new(),
                blocks: Vec::new(),
                block_of: Vec::new(),
                vars: Vec::new(),
                intrinsics: Vec::new(),
            },
            var_index: Default::default(),
            next_source: 0,
        }
    }

    pub fn name(&mut self, name: &str) -> &mut Self {
        self.f.name = name.to_string();
        self
    }

    pub fn start(&mut self, start: u64) -> &mut Self {
        self.f.start = start;
        self
    }

    pub fn address_size(&mut self, size: u8) -> &mut Self {
        self.f.address_size = size;
        self
    }

    /// The variable with the host's identity `(source_type, index, storage)`, created on first use.
    pub fn var(&mut self, source_type: u32, index: u32, storage: i64, name: &str, ty: Option<TypeId>) -> VarId {
        let key = (source_type, index, storage);
        if let Some(v) = self.var_index.get(&key) {
            return *v;
        }
        let id = VarId(self.f.vars.len() as u32);
        self.f.vars.push(VarInfo { source_type, index, storage, name: name.to_string(), ty });
        self.var_index.insert(key, id);
        id
    }

    /// A variable known only by name (the fakes).
    pub fn named_var(&mut self, name: &str, ty: Option<TypeId>) -> VarId {
        if let Some(v) = self.f.vars.iter().position(|v| v.name == name) {
            return VarId(v as u32);
        }
        let index = self.f.vars.len() as u32;
        self.var(1, index, 0, name, ty)
    }

    /// Records the name of the intrinsic with the host's `index`.
    pub fn intrinsic_name(&mut self, index: u32, name: &str) {
        if self.f.intrinsic_name(index).is_none() {
            self.f.intrinsics.push((index, name.to_string()));
        }
    }

    /// The index of a named intrinsic, allocated on first use (for fixtures).
    pub fn intern_intrinsic(&mut self, name: &str) -> u32 {
        if let Some((i, _)) = self.f.intrinsics.iter().find(|(_, n)| n == name) {
            return *i;
        }
        let index = self.f.intrinsics.len() as u32;
        self.f.intrinsics.push((index, name.to_string()));
        index
    }

    pub fn set_var_type(&mut self, v: VarId, ty: Option<TypeId>) {
        self.f.vars[v.0 as usize].ty = ty;
    }

    pub fn set_expr_type(&mut self, e: ExprId, ty: Option<TypeId>) {
        self.f.exprs[e.0 as usize].ty = ty;
    }

    pub fn set_address(&mut self, e: ExprId, address: u64) {
        self.f.exprs[e.0 as usize].address = address;
    }

    pub fn expr_op(&self, e: ExprId) -> Op {
        self.f.exprs[e.0 as usize].op
    }

    pub fn expr_size(&self, e: ExprId) -> u16 {
        self.f.exprs[e.0 as usize].size
    }

    pub fn var_count(&self) -> usize {
        self.f.vars.len()
    }

    /// A list operand holding `items`.
    pub fn list(&mut self, items: &[Operand]) -> Operand {
        let start = self.f.lists.len() as u32;
        self.f.lists.extend_from_slice(items);
        Operand::List { start, len: items.len() as u32 }
    }

    /// An expression; `source` is the host's index for it (None: a fresh one).
    pub fn expr_at(&mut self, op: Op, size: u16, address: u64, source: Option<u32>, operands: &[Operand]) -> ExprId {
        let source = source.unwrap_or_else(|| {
            self.next_source += 1;
            self.next_source
        });
        let start = self.f.operands.len() as u32;
        self.f.operands.extend_from_slice(operands);
        self.f.exprs.push(Expr {
            op,
            size,
            source,
            instr: u32::MAX,
            address,
            source_operand: 0,
            ty: None,
            operands: start,
            operand_count: operands.len() as u8,
        });
        ExprId(self.f.exprs.len() as u32 - 1)
    }

    pub fn expr(&mut self, op: Op, size: u16, operands: &[Operand]) -> ExprId {
        self.expr_at(op, size, 0, None, operands)
    }

    pub fn set_source_operand(&mut self, id: ExprId, source_operand: u32) {
        self.f.exprs[id.0 as usize].source_operand = source_operand;
    }

    /// Appends an instruction whose root is `root`; every expression of its tree
    /// is stamped with the instruction index.
    pub fn instr(&mut self, root: ExprId) -> u32 {
        let index = self.f.instrs.len() as u32;
        self.f.instrs.push(root);
        let mut stack = vec![root];
        while let Some(e) = stack.pop() {
            self.f.exprs[e.0 as usize].instr = index;
            if self.f.exprs[e.0 as usize].address == 0 {
                self.f.exprs[e.0 as usize].address = self.f.exprs[root.0 as usize].address;
            }
            let ops: Vec<Operand> = self.f.operands(e).to_vec();
            for o in ops {
                self.push_sub_operands(o, &mut stack);
            }
        }
        index
    }

    fn push_sub_operands(&self, o: Operand, stack: &mut Vec<ExprId>) {
        match o {
            Operand::Expr(e) => stack.push(e),
            Operand::List { .. } => {
                for item in self.f.list(o) {
                    self.push_sub_operands(*item, stack);
                }
            }
            _ => {}
        }
    }

    pub fn instr_count(&self) -> u32 {
        self.f.instrs.len() as u32
    }

    /// A basic block over instructions `start..end`.
    pub fn block(&mut self, start: u32, end: u32) -> BlockId {
        let id = BlockId(self.f.blocks.len() as u32);
        self.f.blocks.push(Block { id, start, end, outgoing: Vec::new(), incoming: Vec::new() });
        id
    }

    pub fn edge(&mut self, kind: BranchKind, source: BlockId, target: BlockId) {
        let edge = Edge { kind, source, target };
        self.f.blocks[source.0 as usize].outgoing.push(edge);
        self.f.blocks[target.0 as usize].incoming.push(edge);
    }

    pub fn finish(mut self) -> Function {
        let mut block_of = vec![BlockId(u32::MAX); self.f.instrs.len()];
        for b in &self.f.blocks {
            for i in b.start..b.end {
                if let Some(slot) = block_of.get_mut(i as usize) {
                    *slot = b.id;
                }
            }
        }
        // Instructions no block claims (never for a finalized function) belong to a
        // block of their own so that lookups stay total.
        for (i, slot) in block_of.iter_mut().enumerate() {
            if slot.0 == u32::MAX {
                let id = BlockId(self.f.blocks.len() as u32);
                self.f.blocks.push(Block { id, start: i as u32, end: i as u32 + 1, outgoing: Vec::new(), incoming: Vec::new() });
                *slot = id;
            }
        }
        self.f.block_of = block_of;
        self.f
    }
}

/// Operand slot widths: how many raw slots the operands of `op` take, in order.
pub fn slot_layout(op: Op) -> impl Iterator<Item = (OperandKind, usize)> {
    op.layout().iter().map(|k| (*k, k.slots()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builds_and_reads() {
        let mut b = Builder::new();
        let s = b.named_var("s", None);
        let r = b.named_var("r", None);
        let vs = b.expr(Op::Var, 8, &[Operand::Var(s)]);
        let c = b.expr(Op::Const, 8, &[Operand::Int(0x17)]);
        let add = b.expr(Op::Add, 8, &[Operand::Expr(vs), Operand::Expr(c)]);
        let ld = b.expr(Op::Load, 1, &[Operand::Expr(add)]);
        let set = b.expr(Op::SetVar, 8, &[Operand::Var(r), Operand::Expr(ld)]);
        let i = b.instr(set);
        let blk = b.block(0, 1);
        let f = b.finish();
        assert_eq!(i, 0);
        assert_eq!(f.block_of(0).id, blk);
        assert_eq!(f.vars_written(set).as_slice(), &[r]);
        assert_eq!(f.vars_read(set).as_slice(), &[s]);
        assert_eq!(f.const_value(c), Some(0x17));
        assert_eq!(f.subtree(set), vec![set, ld, add, vs, c]);
        assert!(f.expr_equal(ld, ld, false));
        assert_eq!(f.instr_of(c), 0);
    }
}
