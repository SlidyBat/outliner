//! Executing a rewrite plan: build a fresh MLIL function, copy every
//! instruction the plan keeps, emit the calls it prescribes, then finalize,
//! regenerate SSA and hand the new function to the analysis context together
//! with the LLIL-SSA maps the core wants.

use std::collections::{BTreeMap, HashMap, HashSet};

use binaryninjacore_sys::*;
use outliner_core::il::{ExprId, Function, Operand, VarId};
use outliner_core::ops::{Op, OperandKind};
use outliner_core::plan::{Action, Assign, Emit, EmitCall, Plan, PlanVar};

use crate::ffi::{cstr, log_debug, var_identifier, Block, Func, Llil, Mlil, TypeRef};
use crate::snapshot::{bn_var, Snapshot};
use crate::types::TypeTable;

/// The function a pattern outlines to: its address and type.
pub struct Target {
    pub addr: u64,
    pub ty: TypeRef,
}

/// The register value state of zero-extended constant data.
const CONSTANT_DATA_ZERO_EXTEND: u64 = 32769;

const POINTER_ARITH: &[Op] = &[Op::Add, Op::Sub, Op::And, Op::Or, Op::Xor, Op::Mul, Op::Lsl, Op::Neg, Op::Not];

/// A source location: the address and operand of the instruction an
/// expression is built from, and that instruction's root expression.
#[derive(Copy, Clone)]
struct Loc {
    address: u64,
    operand: u32,
    /// The old expression the new one maps to.
    source: u32,
    /// The old instruction a new instruction maps to.
    instr: u32,
}

struct FreshVar {
    var: BNVariable,
    width: u16,
}

/// A variable the rewrite introduced for a call's result.
#[derive(Clone)]
pub struct FreshInfo {
    pub var: BNVariable,
    pub name: String,
    pub ty: Option<TypeRef>,
}

/// A rewritten function before it is installed: the new MLIL, the maps the
/// core wants with it, and the variable changes that go with it.
pub struct Built {
    pub mlil: Mlil,
    instr_map: BTreeMap<u32, Vec<usize>>,
    expr_map: BTreeMap<u32, Vec<usize>>,
    pub fresh: Vec<FreshInfo>,
    /// Variables to give a call's return type: (variable, type, name).
    pub retype: Vec<(BNVariable, TypeRef, String)>,
    pub count: usize,
    pub times: ApplyTimes,
}

struct Rewriter<'a> {
    old: &'a Mlil,
    new: Mlil,
    func: &'a Func,
    snap: &'a Snapshot,
    f: &'a Function,
    types: &'a TypeTable,
    targets: &'a [Option<Target>],
    arch: *mut BNArchitecture,
    addr_size: u16,
    fresh: Vec<FreshVar>,
    fresh_info: Vec<FreshInfo>,
    /// New instruction indexes built from each old instruction.
    instr_map: BTreeMap<u32, Vec<usize>>,
    /// New expression indexes built from each old expression.
    expr_map: BTreeMap<u32, Vec<usize>>,
}

impl Rewriter<'_> {
    // -- widths and variables ----------------------------------------------------------

    fn var_width(&self, v: VarId) -> u16 {
        match self.f.var(v).ty {
            Some(t) => {
                let w = self.types.get(t).width() as u16;
                if w != 0 {
                    w
                } else {
                    self.addr_size
                }
            }
            None => self.addr_size,
        }
    }

    fn plan_var(&self, v: PlanVar) -> (u64, u16) {
        match v {
            PlanVar::Existing(v) => (var_identifier(&bn_var(self.f.var(v))), self.var_width(v)),
            PlanVar::Fresh(k) => (var_identifier(&self.fresh[k].var), self.fresh[k].width),
        }
    }

    fn loc_of(&self, e: ExprId) -> Loc {
        let x = self.f.expr(e);
        Loc { address: x.address, operand: x.source_operand, source: x.source, instr: x.instr }
    }

    // -- raw building ------------------------------------------------------------------

    fn expr(&mut self, op: Op, size: u16, loc: Loc, slots: [u64; 5]) -> u64 {
        let operation: BNMediumLevelILOperation = unsafe { std::mem::transmute(op as u8) };
        let index = unsafe {
            BNMediumLevelILAddExprWithLocation(
                self.new.raw(),
                operation,
                loc.address,
                loc.operand,
                size as usize,
                slots[0],
                slots[1],
                slots[2],
                slots[3],
                slots[4],
            )
        };
        self.expr_map.entry(loc.source).or_default().push(index);
        index as u64
    }

    fn append(&mut self, expr: u64, loc: Loc) {
        let index = unsafe { BNMediumLevelILAddInstruction(self.new.raw(), expr as usize) };
        self.instr_map.entry(loc.instr).or_default().push(index);
    }

    fn operand_list(&mut self, items: &[u64]) -> u64 {
        let mut items = items.to_vec();
        unsafe { BNMediumLevelILAddOperandList(self.new.raw(), items.as_mut_ptr(), items.len()) as u64 }
    }

    fn label_for(&self, instr: u32) -> Option<*mut BNMediumLevelILLabel> {
        let label = unsafe { BNGetLabelForMediumLevelILSourceInstruction(self.new.raw(), instr as usize) };
        (!label.is_null()).then_some(label)
    }

    fn set_address(&mut self, address: u64) {
        unsafe { BNMediumLevelILSetCurrentAddress(self.new.raw(), self.arch, address) }
    }

    fn goto(&mut self, label: *mut BNMediumLevelILLabel, loc: Loc) -> u64 {
        let index = unsafe { BNMediumLevelILGotoWithLocation(self.new.raw(), label, loc.address, loc.operand) };
        self.expr_map.entry(loc.source).or_default().push(index);
        index as u64
    }

    fn if_expr(&mut self, cond: u64, t: *mut BNMediumLevelILLabel, f: *mut BNMediumLevelILLabel, loc: Loc) -> u64 {
        let index = unsafe { BNMediumLevelILIfWithLocation(self.new.raw(), cond, t, f, loc.address, loc.operand) };
        self.expr_map.entry(loc.source).or_default().push(index);
        index as u64
    }

    fn const_(&mut self, size: u16, value: i64, loc: Loc) -> u64 {
        self.expr(Op::Const, size, loc, [value as u64, 0, 0, 0, 0])
    }

    fn const_pointer(&mut self, size: u16, value: u64, loc: Loc) -> u64 {
        self.expr(Op::ConstPtr, size, loc, [value, 0, 0, 0, 0])
    }

    fn var_read(&mut self, v: PlanVar, size: u16, loc: Loc) -> (u64, u16) {
        let (id, width) = self.plan_var(v);
        let size = if size != 0 { size } else { width };
        (self.expr(Op::Var, size, loc, [id, 0, 0, 0, 0]), size)
    }

    // -- copying -----------------------------------------------------------------------

    /// Copies an old expression.  `replacements` swaps sub-expressions for
    /// variable reads; `address` widens what feeds a structure access to
    /// pointer width, as an argument needs.
    fn copy(&mut self, e: ExprId, replacements: Option<&BTreeMap<ExprId, PlanVar>>, instr_loc: Loc, address: bool) -> u64 {
        if let Some(v) = replacements.and_then(|r| r.get(&e)) {
            return self.var_read(*v, self.f.size(e), instr_loc).0;
        }
        let f = self.f;
        let op = f.op(e);
        let size = f.size(e);
        let loc = self.loc_of(e);
        if address && size != 0 && size < self.addr_size {
            if matches!(op, Op::Const | Op::ConstPtr) {
                return self.const_(self.addr_size, f.const_value(e).unwrap_or(0), loc);
            }
            if POINTER_ARITH.contains(&op) && f.operands(e).iter().all(|o| matches!(o, Operand::Expr(_))) {
                let mut slots = [0u64; 5];
                for (k, o) in f.operands(e).iter().enumerate() {
                    if let Operand::Expr(sub) = o {
                        slots[k] = self.copy(*sub, replacements, instr_loc, address);
                    }
                }
                return self.expr(op, self.addr_size, loc, slots);
            }
        }
        let index = match op {
            Op::Goto => {
                let target = f.goto_target(e).unwrap_or(0);
                match self.label_for(target) {
                    Some(label) => self.goto(label, loc),
                    None => {
                        let dest = self.const_pointer(self.addr_size, f.expr(f.instr(target)).address, loc);
                        self.expr(Op::Jump, 0, loc, [dest, 0, 0, 0, 0])
                    }
                }
            }
            Op::If => {
                let (t, fl) = f.if_targets(e).unwrap_or((0, 0));
                match (self.label_for(t), self.label_for(fl)) {
                    (Some(lt), Some(lf)) => {
                        let cond = f.sub(e, 0).map(|c| self.copy(c, replacements, instr_loc, address)).unwrap_or(0);
                        self.if_expr(cond, lt, lf, loc)
                    }
                    _ => self.expr(Op::Undef, 0, loc, [0; 5]),
                }
            }
            Op::JumpTo => {
                let dest = f.sub(e, 0).map(|d| self.copy(d, replacements, instr_loc, address)).unwrap_or(0);
                let pairs: Vec<i64> = f.list(f.operand(e, 1)).iter().filter_map(|o| if let Operand::Int(v) = o { Some(*v) } else { None }).collect();
                let mut values = Vec::new();
                let mut labels = Vec::new();
                let mut complete = true;
                for pair in pairs.chunks_exact(2) {
                    match self.label_for(pair[1] as u32) {
                        Some(label) => {
                            values.push(pair[0] as u64);
                            labels.push(label);
                        }
                        None => complete = false,
                    }
                }
                if complete {
                    let map = unsafe { BNMediumLevelILAddLabelMap(self.new.raw(), values.as_mut_ptr(), labels.as_mut_ptr(), labels.len()) };
                    self.expr(Op::JumpTo, 0, loc, [dest, (labels.len() * 2) as u64, map as u64, 0, 0])
                } else {
                    self.expr(Op::Jump, 0, loc, [dest, 0, 0, 0, 0])
                }
            }
            Op::Assert => {
                let var = f.var_operand(e, 0).map(|v| var_identifier(&bn_var(f.var(v)))).unwrap_or(0);
                let constraint = match f.operand(e, 1) {
                    Operand::Constraint(c) => c,
                    _ => 0,
                };
                let cached = unsafe {
                    let mut pvs = BNGetCachedMediumLevelILPossibleValueSet(self.old.raw(), constraint as usize);
                    let index = BNCacheMediumLevelILPossibleValueSet(self.new.raw(), &mut pvs);
                    BNFreePossibleValueSet(&mut pvs);
                    index
                };
                self.expr(Op::Assert, size, loc, [var, cached as u64, 0, 0, 0])
            }
            _ => {
                let mut slots = [0u64; 5];
                let mut k = 0usize;
                let operands: Vec<Operand> = f.operands(e).to_vec();
                for (kind, operand) in op.layout().iter().zip(operands) {
                    match (kind, operand) {
                        (OperandKind::Expr, Operand::Expr(sub)) => slots[k] = self.copy(sub, replacements, instr_loc, address),
                        (OperandKind::Var, Operand::Var(v)) => slots[k] = var_identifier(&bn_var(f.var(v))),
                        (OperandKind::Int, Operand::Int(v)) => slots[k] = v as u64,
                        (OperandKind::Float, Operand::Float(v)) => slots[k] = v,
                        (OperandKind::Intrinsic, Operand::Intrinsic(v)) => slots[k] = v as u64,
                        (OperandKind::ExprList, list @ Operand::List { .. }) => {
                            let items: Vec<u64> = f
                                .list(list)
                                .to_vec()
                                .into_iter()
                                .filter_map(|o| if let Operand::Expr(sub) = o { Some(sub) } else { None })
                                .map(|sub| self.copy(sub, replacements, instr_loc, address))
                                .collect();
                            slots[k] = items.len() as u64;
                            slots[k + 1] = self.operand_list(&items);
                        }
                        (OperandKind::VarList, list @ Operand::List { .. }) => {
                            let items: Vec<u64> = f
                                .list(list)
                                .iter()
                                .filter_map(|o| if let Operand::Var(v) = o { Some(var_identifier(&bn_var(f.var(*v)))) } else { None })
                                .collect();
                            slots[k] = items.len() as u64;
                            slots[k + 1] = self.operand_list(&items);
                        }
                        (OperandKind::IntList | OperandKind::TargetMap, list @ Operand::List { .. }) => {
                            let items: Vec<u64> =
                                f.list(list).iter().filter_map(|o| if let Operand::Int(v) = o { Some(*v as u64) } else { None }).collect();
                            slots[k] = items.len() as u64;
                            slots[k + 1] = self.operand_list(&items);
                        }
                        (OperandKind::ConstantData, Operand::ConstData { state, value }) => {
                            slots[k] = state as u64;
                            slots[k + 1] = value as u64;
                        }
                        (_, Operand::Raw(v)) => slots[k] = v,
                        _ => {}
                    }
                    k += kind.slots();
                }
                self.expr(op, size, loc, slots)
            }
        };
        let attributes = self.snap.attributes.get(e.0 as usize).copied().unwrap_or(0);
        if attributes != 0 {
            unsafe { BNSetMediumLevelILExprAttributes(self.new.raw(), index as usize, attributes) }
        }
        index
    }

    // -- emitting --------------------------------------------------------------------

    /// Builds an emit tree; returns the expression and its width.
    fn emit(&mut self, node: &Emit, parent_size: u16, loc: Loc) -> (u64, u16) {
        let addr = self.addr_size;
        match node {
            Emit::Copy(e) => {
                let size = self.f.size(*e);
                (self.copy(*e, None, loc, false), if size != 0 { size } else { addr })
            }
            Emit::CopyAddress(e) => (self.copy(*e, None, loc, true), addr),
            Emit::Var(v) => self.var_read(*v, 0, loc),
            Emit::VarSized(v, size) => self.var_read(*v, *size, loc),
            Emit::AddressOf(v) => {
                let id = var_identifier(&bn_var(self.f.var(*v)));
                (self.expr(Op::AddressOf, 0, loc, [id, 0, 0, 0, 0]), addr)
            }
            Emit::AddressOfField(v, offset) => {
                let id = var_identifier(&bn_var(self.f.var(*v)));
                (self.expr(Op::AddressOfField, 0, loc, [id, *offset as u64, 0, 0, 0]), addr)
            }
            Emit::Const(size, value) => {
                let size = size.unwrap_or(parent_size);
                let size = if size != 0 { size } else { addr };
                (self.const_(size, *value, loc), size)
            }
            Emit::ConstPtr(value) => (self.const_pointer(addr, *value, loc), addr),
            Emit::ConstData { size, value } => (self.expr(Op::ConstData, *size, loc, [CONSTANT_DATA_ZERO_EXTEND, *value, 0, 0, 0]), *size),
            Emit::PtrAdd(base, offset) => {
                let (b, _) = self.emit(base, addr, loc);
                let c = self.const_(addr, *offset, loc);
                (self.expr(Op::Add, addr, loc, [b, c, 0, 0, 0]), addr)
            }
            Emit::Op { op, size, args } => {
                // An operation without a size takes its first sized operand's width.
                let mut width = size.unwrap_or(0);
                let mut built: Vec<Option<u64>> = Vec::with_capacity(args.len());
                for arg in args {
                    if matches!(arg, Emit::Const(None, _)) {
                        built.push(None);
                        continue;
                    }
                    let (index, w) = self.emit(arg, width, loc);
                    built.push(Some(index));
                    if width == 0 {
                        width = w;
                    }
                }
                let width = if width != 0 { width } else { addr };
                let mut slots = [0u64; 5];
                for (k, (arg, index)) in args.iter().zip(built).enumerate() {
                    slots[k] = match (arg, index) {
                        (Emit::Const(None, value), None) => self.const_(width, *value, loc),
                        (_, Some(index)) => index,
                        _ => 0,
                    };
                }
                (self.expr(*op, width, loc, slots), width)
            }
        }
    }

    fn emit_call(&mut self, call: &EmitCall, loc: Loc) -> Result<(), String> {
        let target = self.targets[call.pattern].as_ref().ok_or("no call target")?;
        let addr_size = self.addr_size;
        let (target_addr, addr) = (target.addr, addr_size);
        let mut args = Vec::with_capacity(call.args.len());
        for arg in &call.args {
            args.push(self.emit(arg, addr, loc).0);
        }
        let mut outputs = Vec::with_capacity(call.outputs.len());
        for (v, size) in &call.outputs {
            let (id, width) = self.plan_var(*v);
            let size = if *size != 0 { *size } else { width };
            outputs.push(self.expr(Op::VarOutput, size, loc, [id, 0, 0, 0, 0]));
        }
        let dest = self.const_pointer(addr, target_addr, loc);
        let outputs_list = self.operand_list(&outputs);
        let args_list = self.operand_list(&args);
        let call_expr = self.expr(Op::Call, 0, loc, [outputs.len() as u64, outputs_list, dest, args.len() as u64, args_list]);
        self.append(call_expr, loc);
        Ok(())
    }

    fn emit_assign(&mut self, assign: &Assign, loc: Loc) {
        let (id, width) = self.plan_var(assign.var);
        let size = if assign.size != 0 { assign.size } else { width };
        let (value, _) = self.emit(&assign.value, size, loc);
        let set = self.expr(Op::SetVar, size, loc, [id, value, 0, 0, 0]);
        self.append(set, loc);
    }

    fn emit_goto(&mut self, target: u32, loc: Loc, what: &str) -> Result<(), String> {
        let label = self.label_for(target).ok_or_else(|| format!("no label for {what} {target}"))?;
        let g = self.goto(label, loc);
        self.append(g, loc);
        Ok(())
    }

    /// Chooses the fresh variables; `create` adds them to the function (a
    /// preview builds a scratch copy and leaves the function alone).
    fn allocate_fresh(&mut self, plan: &Plan, create: bool) -> Result<(), String> {
        // Fresh variables are register variables the function does not use yet.
        let register = BNVariableSourceType::RegisterVariableSourceType;
        let mut next_index: BTreeMap<i64, u32> = BTreeMap::new();
        let mut default_storage: Option<i64> = None;
        for v in &self.f.vars {
            if v.source_type == register as u32 {
                let slot = next_index.entry(v.storage).or_insert(0);
                *slot = (*slot).max(v.index + 1);
                default_storage.get_or_insert(v.storage);
            }
        }
        let default_storage = default_storage.unwrap_or(0);
        for fresh in &plan.fresh {
            let target = self.targets[fresh.pattern].as_ref().ok_or("no call target for a fresh variable")?;
            let mut storage = default_storage;
            if let Some(example) = fresh.example {
                if self.f.op(example) == Op::Var {
                    if let Some(v) = self.f.var_of(example) {
                        let info = self.f.var(v);
                        if info.source_type == register as u32 {
                            storage = info.storage;
                        }
                    }
                }
            }
            let index = *next_index.get(&storage).unwrap_or(&1);
            next_index.insert(storage, index + 1);
            let var = BNVariable { type_: register, index, storage };
            let ret_type = target.ty.child();
            let mut width = self.addr_size;
            if let Some(ret) = &ret_type {
                if create {
                    self.func.create_auto_var(&var, ret, &fresh.name);
                }
                let w = ret.width() as u16;
                if w != 0 {
                    width = w;
                }
            }
            self.fresh.push(FreshVar { var, width });
            self.fresh_info.push(FreshInfo { var, name: fresh.name.clone(), ty: ret_type });
        }
        Ok(())
    }

    fn build(&mut self, plan: &Plan, old_blocks: &HashMap<u32, Block>) -> Result<(), String> {
        let f = self.f;
        // The block that will be emitted right after each block, so that a goto to
        // it can be left out (control falls through in the new function).
        let mut next_emitted: HashMap<u32, Option<u32>> = HashMap::new();
        let mut following: Option<u32> = None;
        for b in f.blocks.iter().rev() {
            next_emitted.insert(b.start, following);
            if !plan.removed_blocks.contains(b.id.0 as usize) {
                following = Some(b.start);
            }
        }
        for block in &f.blocks {
            if plan.removed_blocks.contains(block.id.0 as usize) {
                continue;
            }
            let handle = old_blocks.get(&block.start).ok_or("missing source block")?;
            unsafe { BNPrepareToCopyMediumLevelILBasicBlock(self.new.raw(), handle.raw()) };
            let next = next_emitted.get(&block.start).copied().flatten();
            for index in block.start..block.end {
                let root = f.instr(index);
                let loc = self.loc_of(root);
                self.set_address(loc.address);
                match plan.actions.get(&index) {
                    Some(Action::Outline { entry_index, call, results, branch, exit_goto }) => {
                        let entry_loc = self.loc_of(f.instr(*entry_index));
                        self.set_address(entry_loc.address);
                        self.emit_call(call, entry_loc)?;
                        for assign in results {
                            self.emit_assign(assign, entry_loc);
                        }
                        if let Some(b) = branch {
                            let (cond, _) = self.emit(&b.cond, self.addr_size, entry_loc);
                            let leave = self.label_for(b.leave);
                            let stay = self.label_for(b.stay);
                            let (Some(leave), Some(stay)) = (leave, stay) else {
                                return Err(format!("no label for branch targets {}/{}", b.leave, b.stay));
                            };
                            let i = self.if_expr(cond, leave, stay, entry_loc);
                            self.append(i, entry_loc);
                        } else if let Some(exit) = exit_goto {
                            if next != Some(*exit) {
                                self.emit_goto(*exit, entry_loc, "join instruction")?;
                            }
                        }
                    }
                    Some(Action::Sites { calls, whole, replacements }) => {
                        for call in calls {
                            self.emit_call(call, loc)?;
                        }
                        if let Some(call) = whole {
                            self.emit_call(call, loc)?;
                        } else {
                            let copied = self.copy(root, Some(replacements), loc, false);
                            self.append(copied, loc);
                        }
                    }
                    Some(Action::Fused { calls, assignments, goto }) => {
                        for call in calls {
                            self.emit_call(call, loc)?;
                        }
                        for assign in assignments {
                            self.emit_assign(assign, loc);
                        }
                        if let Some(kept) = goto {
                            if next != Some(*kept) {
                                self.emit_goto(*kept, loc, "block")?;
                            }
                        }
                    }
                    Some(Action::Replace { replacements }) => {
                        if !plan.skip.contains(index as usize) {
                            let copied = self.copy(root, Some(replacements), loc, false);
                            self.append(copied, loc);
                        }
                    }
                    None => {
                        if !plan.skip.contains(index as usize) {
                            let copied = self.copy(root, None, loc, false);
                            self.append(copied, loc);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    // -- committing ------------------------------------------------------------------

    /// Hands the new function to the context with the LLIL-SSA maps the core
    /// derives its cross-level lookups from.
    fn commit(old: &Mlil, built: &Built, context: *mut BNAnalysisContext) {
        let llil_ssa: Option<Llil> = old.llil().and_then(|l| l.ssa_form());
        let (llil_instr_count, llil_expr_count) = llil_ssa
            .as_ref()
            .map(|l| unsafe { (BNGetLowLevelILInstructionCount(l.raw()), BNGetLowLevelILExprCount(l.raw())) })
            .unwrap_or((0, 0));
        let reverse_mlil: Option<Mlil> =
            llil_ssa.as_ref().and_then(|l| unsafe { Mlil::owned(BNGetMediumLevelILForLowLevelIL(l.raw())) });
        let reverse_count = reverse_mlil.as_ref().map(|m| m.expr_count()).unwrap_or(0);

        // Instructions map one to one.
        let mut instr_map: Vec<usize> = Vec::new();
        for (old_instr, new_indexes) in &built.instr_map {
            let llil_index = old.llil_instruction_index(*old_instr as usize);
            if llil_index >= llil_instr_count {
                continue;
            }
            for new_index in new_indexes {
                if instr_map.len() <= llil_index {
                    instr_map.resize(llil_index + 1, usize::MAX);
                }
                instr_map[llil_index] = *new_index;
            }
        }

        // Expressions: every LLIL-SSA expression behind an old expression maps
        // to the new expressions built from it.
        let mut reverse_memo: HashMap<usize, (Option<usize>, HashSet<usize>)> = HashMap::new();
        let mut expr_map: Vec<BNExprMapInfo> = Vec::new();
        if let Some(llil) = &llil_ssa {
            for (old_expr, new_indexes) in &built.expr_map {
                let old_expr = *old_expr as usize;
                let direct = old.llil_expr_index(old_expr);
                let direct = (direct < llil_expr_count).then_some(direct);
                for old_index in old.llil_expr_indexes(old_expr) {
                    let (reverse_direct, reverse_all) = reverse_memo.entry(old_index).or_insert_with(|| {
                        let d = llil.mlil_expr_index(old_index);
                        let d = (d < reverse_count).then_some(d);
                        (d, llil.mlil_expr_indexes(old_index).into_iter().collect())
                    });
                    for new_index in new_indexes {
                        expr_map.push(BNExprMapInfo {
                            lowerIndex: old_index,
                            higherIndex: *new_index,
                            mapLowerToHigher: reverse_all.contains(&old_expr),
                            mapHigherToLower: true,
                            lowerToHigherDirect: *reverse_direct == Some(old_expr),
                            higherToLowerDirect: Some(old_index) == direct,
                        });
                    }
                }
            }
        }
        unsafe {
            BNSetMediumLevelILFunction(context, built.mlil.raw(), instr_map.as_mut_ptr(), instr_map.len(), expr_map.as_mut_ptr(), expr_map.len());
        }
    }
}

/// Timing of the rewrite's steps, in seconds.
#[derive(Default, Clone, Copy)]
pub struct ApplyTimes {
    pub build: f64,
    pub finalize: f64,
    pub ssa: f64,
    pub commit: f64,
    pub retype: f64,
}

/// Builds the rewritten function for `plan` without installing it.  With
/// `create_vars` the fresh variables are added to the function (what the
/// workflow does); a preview leaves the function untouched.
pub fn build_rewrite(
    old: &Mlil,
    func: &Func,
    snap: &Snapshot,
    types: &TypeTable,
    plan: &Plan,
    targets: &[Option<Target>],
    create_vars: bool,
) -> Result<Built, String> {
    let mut times = ApplyTimes::default();
    let mut clock = crate::workflow::Clock::start();
    let arch = func.arch();
    let llil = old.llil();
    let new = unsafe { Mlil::owned(BNCreateMediumLevelILFunction(arch, func.raw(), llil.as_ref().map_or(std::ptr::null_mut(), |l| l.raw()))) }
        .ok_or("could not create an MLIL function")?;
    unsafe { BNPrepareToCopyMediumLevelILFunction(new.raw(), old.raw()) };
    let old_blocks: HashMap<u32, Block> = old.basic_blocks().into_iter().map(|b| (b.start() as u32, b)).collect();
    let mut rewriter = Rewriter {
        old,
        new,
        func,
        snap,
        f: &snap.f,
        types,
        targets,
        arch,
        addr_size: func.address_size() as u16,
        fresh: Vec::new(),
        fresh_info: Vec::new(),
        instr_map: BTreeMap::new(),
        expr_map: BTreeMap::new(),
    };
    rewriter.allocate_fresh(plan, create_vars)?;
    rewriter.build(plan, &old_blocks)?;
    times.build = clock.lap();
    unsafe { BNFinalizeMediumLevelILFunction(rewriter.new.raw()) };
    times.finalize = clock.lap();
    unsafe {
        BNGenerateMediumLevelILSSAForm(rewriter.new.raw(), true, true, std::ptr::null_mut(), 0, std::ptr::null_mut(), 0);
    }
    times.ssa = clock.lap();
    let mut retype = Vec::new();
    for (v, pattern) in &plan.retype {
        if let Some(target) = &targets[*pattern] {
            if let Some((ret, name)) = retype_needed(&snap.f, types, *v, &target.ty) {
                retype.push((bn_var(snap.f.var(*v)), ret, name));
            }
        }
    }
    Ok(Built { mlil: rewriter.new, instr_map: rewriter.instr_map, expr_map: rewriter.expr_map, fresh: rewriter.fresh_info, retype, count: plan.count, times })
}

/// Installs a built function in the analysis context and applies its
/// variable retyping; returns how many regions were outlined and the times.
pub fn commit_rewrite(context: *mut BNAnalysisContext, old: &Mlil, func: &Func, built: Built) -> (usize, ApplyTimes) {
    let mut times = built.times;
    let mut clock = crate::workflow::Clock::start();
    Rewriter::commit(old, &built, context);
    times.commit = clock.lap();
    for (var, ret, name) in &built.retype {
        func.create_auto_var(var, ret, name);
        log_debug(&format!("retyped {name} to {} in {}", ret.text(), func.name()));
    }
    times.retype = clock.lap();
    (built.count, times)
}

/// Executes `plan` on `old` and installs the result; returns how many regions
/// were outlined and where the time went.
pub fn apply_plan(
    context: *mut BNAnalysisContext,
    old: &Mlil,
    func: &Func,
    snap: &Snapshot,
    types: &TypeTable,
    plan: &Plan,
    targets: &[Option<Target>],
) -> Result<(usize, ApplyTimes), String> {
    let built = build_rewrite(old, func, snap, types, plan, targets, true)?;
    Ok(commit_rewrite(context, old, func, built))
}

/// The return type a result variable should get, with its name, when its
/// current type differs.
fn retype_needed(f: &Function, types: &TypeTable, v: VarId, func_type: &TypeRef) -> Option<(TypeRef, String)> {
    let ret = func_type.child()?;
    if ret.class() == BNTypeClass::VoidTypeClass {
        return None;
    }
    let info = f.var(v);
    if let Some(current) = info.ty {
        if types.get(current) == &ret {
            return None;
        }
    }
    Some((ret, info.name.clone()))
}

/// Tell the core about every call to an outlined target left in the function
/// so cross-references exist.  Done once after the last round: a call one
/// round hoists may be consumed by a later round's expression pattern, and a
/// reference recorded for it would outlive the call.
pub fn record_references(context: *mut BNAnalysisContext, mlil: &Mlil, arch_name: &str, targets: &HashSet<u64>) -> usize {
    let mut count = 0;
    let arch = serde_json::to_string(arch_name).unwrap_or_default();
    for i in 0..mlil.instruction_count() {
        let raw = mlil.raw_expr(mlil.expr_for_instruction(i));
        if !matches!(Op::from_u32(raw.operation as u32), Some(Op::Call) | Some(Op::Tailcall)) {
            continue;
        }
        let dest = mlil.raw_expr(raw.operands[2] as usize);
        if Op::from_u32(dest.operation as u32) != Some(Op::ConstPtr) {
            continue;
        }
        let addr = dest.operands[0];
        if !targets.contains(&addr) {
            continue;
        }
        let request = format!("[\"directRefs\",\"insert\",{addr},{arch},{}]", raw.address);
        if unsafe { BNAnalysisContextInform(context, cstr(&request).as_ptr()) } {
            count += 1;
        } else {
            log_debug(&format!("could not record reference to {addr:#x} from {:#x}", raw.address));
        }
    }
    count
}
