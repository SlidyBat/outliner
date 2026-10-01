//! Reading a Binary Ninja MLIL function into the core's flat snapshot.
//!
//! The snapshot is read once per round and dropped with it.  Expression
//! indexes of the source function are kept as each expression's `source`, so
//! the environment and the rewriter can go back to the core's objects.

use std::collections::HashMap;

use binaryninjacore_sys::*;
use outliner_core::il::{BranchKind, Builder, ExprId, Function, Operand, VarId, VarInfo};
use outliner_core::ops::{Op, OperandKind};

use crate::ffi::{take_string, var_from_identifier, var_identifier, Func, Mlil};
use crate::types::TypeTable;

/// A function's MLIL as the core sees it, plus what only the rewriter needs.
pub struct Snapshot {
    pub f: Function,
    /// Per expression (by `ExprId`), the core's instruction attributes.
    pub attributes: Vec<u32>,
    /// The function's variables by the core's identifier.
    pub var_ids: HashMap<u64, VarId>,
}

struct Reader<'a> {
    mlil: &'a Mlil,
    func: &'a Func,
    types: &'a mut TypeTable,
    builder: Builder,
    attributes: Vec<u32>,
    var_ids: HashMap<u64, VarId>,
    arch: *mut BNArchitecture,
    overrides: &'a VarOverrides,
}

impl Reader<'_> {
    fn var(&mut self, id: u64) -> VarId {
        if let Some(v) = self.var_ids.get(&id) {
            return *v;
        }
        let var = var_from_identifier(id);
        let (name, ty) = match self.overrides.get(&id) {
            Some((name, ty)) => (name.clone(), ty.clone().map(|t| self.types.intern(t))),
            None => (self.func.var_name(&var), self.func.var_type(&var).map(|t| self.types.intern(t))),
        };
        let v = self.builder.var(var.type_ as u32, var.index, var.storage, &name, ty);
        self.var_ids.insert(id, v);
        v
    }

    fn expr(&mut self, index: usize) -> ExprId {
        let raw = self.mlil.raw_expr(index);
        let op = Op::from_u32(raw.operation as u32).unwrap_or(Op::Undef);
        let slots = raw.operands;
        let mut operands: Vec<Operand> = Vec::with_capacity(op.layout().len());
        let mut k = 0usize;
        for kind in op.layout() {
            let operand = match kind {
                OperandKind::Expr => Operand::Expr(self.expr(slots[k] as usize)),
                OperandKind::Int => Operand::Int(slots[k] as i64),
                OperandKind::Var => Operand::Var(self.var(slots[k])),
                OperandKind::Float => Operand::Float(slots[k]),
                OperandKind::Intrinsic => {
                    let index = slots[k] as u32;
                    let name = unsafe { take_string(BNGetArchitectureIntrinsicName(self.arch, index)) };
                    self.builder.intrinsic_name(index, &name);
                    Operand::Intrinsic(index)
                }
                OperandKind::Constraint => Operand::Constraint(slots[k]),
                OperandKind::ExprList => {
                    let items: Vec<Operand> =
                        self.mlil.operand_list(index, k).into_iter().map(|e| Operand::Expr(self.expr(e as usize))).collect();
                    self.builder.list(&items)
                }
                OperandKind::VarList => {
                    let items: Vec<Operand> =
                        self.mlil.operand_list(index, k).into_iter().map(|id| Operand::Var(self.var(id))).collect();
                    self.builder.list(&items)
                }
                OperandKind::IntList | OperandKind::TargetMap => {
                    let items: Vec<Operand> = self.mlil.operand_list(index, k).into_iter().map(|v| Operand::Int(v as i64)).collect();
                    self.builder.list(&items)
                }
                OperandKind::ConstantData => Operand::ConstData { state: slots[k] as u32, value: slots[k + 1] as i64 },
                // SSA operands never occur in the form the snapshot reads.
                OperandKind::VarSsa | OperandKind::VarSsaDestAndSrc | OperandKind::VarSsaList => Operand::Raw(slots[k]),
            };
            operands.push(operand);
            k += kind.slots();
        }
        let id = self.builder.expr_at(op, raw.size as u16, raw.address, Some(index as u32), &operands);
        self.builder.set_source_operand(id, raw.sourceOperand);
        if self.attributes.len() <= id.0 as usize {
            self.attributes.resize(id.0 as usize + 1, 0);
        }
        self.attributes[id.0 as usize] = raw.attributes;
        id
    }
}

/// Reads `mlil` (the non-SSA form of `func`'s MLIL) into a snapshot.
pub fn read(mlil: &Mlil, func: &Func, types: &mut TypeTable) -> Snapshot {
    read_with(mlil, func, types, &HashMap::new())
}

/// A name and type for a variable the function does not know (one a scratch
/// rewrite introduced without adding it to the function).
pub type VarOverrides = HashMap<u64, (String, Option<crate::ffi::TypeRef>)>;

/// [`read`], with `overrides` standing in for variables the function has no
/// name or type for.
pub fn read_with(mlil: &Mlil, func: &Func, types: &mut TypeTable, overrides: &VarOverrides) -> Snapshot {
    let mut builder = Builder::new();
    builder.name(&func.name()).start(func.start()).address_size(func.address_size() as u8);
    let arch = func.arch();
    let mut reader = Reader { mlil, func, types, builder, attributes: Vec::new(), var_ids: HashMap::new(), arch, overrides };
    for (var, name, ty) in func.variables() {
        let id = var_identifier(&var);
        let ty = ty.map(|t| reader.types.intern(t));
        let v = reader.builder.var(var.type_ as u32, var.index, var.storage, &name, ty);
        reader.var_ids.insert(id, v);
    }
    let count = mlil.instruction_count();
    for i in 0..count {
        let root = reader.expr(mlil.expr_for_instruction(i));
        reader.builder.instr(root);
    }
    let mut blocks = mlil.basic_blocks();
    blocks.sort_by_key(|b| b.index());
    let mut ids = HashMap::with_capacity(blocks.len());
    for block in &blocks {
        let id = reader.builder.block(block.start() as u32, block.end() as u32);
        ids.insert(block.start(), id);
    }
    for block in &blocks {
        let source = ids[&block.start()];
        for (kind, target) in block.outgoing() {
            if let Some(target) = target.and_then(|start| ids.get(&start)) {
                reader.builder.edge(branch_kind(kind), source, *target);
            }
        }
    }
    let attributes = reader.attributes;
    let var_ids = reader.var_ids;
    Snapshot { f: reader.builder.finish(), attributes, var_ids }
}

fn branch_kind(kind: BNBranchType) -> BranchKind {
    match kind {
        BNBranchType::UnconditionalBranch => BranchKind::Unconditional,
        BNBranchType::TrueBranch => BranchKind::True,
        BNBranchType::FalseBranch => BranchKind::False,
        _ => BranchKind::Other,
    }
}

/// The core's variable for a snapshot variable.
pub fn bn_var(info: &VarInfo) -> BNVariable {
    let type_ = match info.source_type {
        0 => BNVariableSourceType::StackVariableSourceType,
        1 => BNVariableSourceType::RegisterVariableSourceType,
        2 => BNVariableSourceType::FlagVariableSourceType,
        3 => BNVariableSourceType::CompositeReturnValueSourceType,
        _ => BNVariableSourceType::CompositeParameterSourceType,
    };
    BNVariable { type_, index: info.index, storage: info.storage }
}
