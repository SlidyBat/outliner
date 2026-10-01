//! What the matcher asks of its host.
//!
//! Everything that needs the real Binary Ninja API (types, symbols, SSA use
//! and definition lists, the bytes of the binary) goes through an [`Env`]
//! supplied by the caller; the unit tests supply one over fake functions.

use std::sync::Arc;

use crate::il::{BlockSet, ExprId, Function, InstrSet, TypeId, VarId};
use crate::pattern::TypeConstraint;

/// One incoming value of a merge (a phi) other than the one being followed.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MergeSource {
    /// The instruction defining it.
    Def(u32),
    /// The value the variable holds on entry to the instruction the query was made at.
    Live,
    /// A parameter, an unknown value.
    Unknown,
}

/// A merge (a phi node) a definition flows into on its way to a read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Merge {
    /// Start of the block that merges.
    pub block_start: u32,
    pub others: Vec<MergeSource>,
}

pub trait Env {
    /// The type of an expression (an `MLIL_VAR` has its variable's type).
    fn type_of_expr(&self, f: &Function, e: ExprId) -> Option<TypeId>;

    fn type_of_var(&self, f: &Function, v: VarId) -> Option<TypeId>;

    /// The type of a pointer to `t` (what a placeholder bound to a variable's address has).
    fn pointer_to(&self, t: TypeId) -> Option<TypeId>;

    /// Whether type `actual` satisfies a placeholder's constraint.
    fn types_match(&self, actual: TypeId, constraint: &TypeConstraint) -> bool;

    /// The printed type, for diagnostics.
    fn type_text(&self, t: TypeId) -> String;

    /// The type spelled for the pattern parser (C++ names escaped); the
    /// printed text unless the host knows better.
    fn type_spelling(&self, t: TypeId) -> String {
        self.type_text(t)
    }

    /// Every name the address has (symbols, the function there).
    fn symbol_names_at(&self, addr: u64) -> Arc<[String]>;

    /// Index of the unique instruction defining the value `var` holds on entry to
    /// `use_index` (a set_var, or a call with that single output), or None.
    fn definition_of(&self, f: &Function, use_index: u32, var: VarId) -> Option<u32>;

    /// Instruction indices that consume the value of `var` defined at `def_index`.
    /// With `kept_blocks`, a use reached only through a merge with a definition
    /// inside those blocks does not count (the other arm is about to be removed).
    fn uses_of(&self, f: &Function, def_index: u32, var: VarId, kept_blocks: Option<&BlockSet>) -> Vec<u32>;

    /// The merges the value of `var` defined at `def_index` flows into,
    /// transitively, on its way to instructions that read it; a merge nothing
    /// reads is not reported.  None when the merge structure cannot be determined.
    fn merges_of(&self, f: &Function, def_index: u32, var: VarId, at_index: u32) -> Option<Vec<Merge>>;

    /// True if `var` written by instruction `instr_index` is used outside `region`.
    fn uses_outside(&self, f: &Function, instr_index: u32, region: &InstrSet, var: VarId) -> bool;

    /// `size` bytes of the binary at `addr`, or None if not all of them are there.
    fn read_bytes(&self, addr: u64, size: usize) -> Option<Vec<u8>>;

    /// An address where the binary holds exactly `data`, or None.
    fn find_bytes(&self, data: &[u8]) -> Option<u64>;

    /// For a structure type (`deref`: the type a pointer or reference leads to),
    /// the member holding byte `offset`: its offset and type, or None.
    fn member_containing(&self, t: TypeId, offset: i64, deref: bool) -> Option<(i64, TypeId)>;

    /// True if instruction `instr` is a call to a function known to be pure.
    fn is_pure_call(&self, f: &Function, instr: u32) -> bool;

    /// The data variable (a global) whose bytes include `addr`: where it
    /// starts and its type.  None when no typed global covers the address.
    fn data_var_containing(&self, _addr: u64) -> Option<(u64, TypeId)> {
        None
    }
}
