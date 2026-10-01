//! MLIL operations and their classification.
//!
//! The enum and the raw operand layouts live in `ops_generated.rs`; this
//! module adds what the matcher, the renderer and the rewriter need to know
//! about an operation beyond its name.

pub use crate::ops_generated::{Op, OperandKind};

/// Operand size suffixes of the pattern language: `b/w/d/q/o` = 1/2/4/8/16 bytes.
pub const SIZE_SUFFIXES: [(&str, u16); 5] = [("b", 1), ("w", 2), ("d", 4), ("q", 8), ("o", 16)];

pub fn size_suffix(size: u16) -> Option<&'static str> {
    SIZE_SUFFIXES.iter().find(|(_, s)| *s == size).map(|(n, _)| *n)
}

pub fn size_from_suffix(text: &str) -> Option<u16> {
    SIZE_SUFFIXES
        .iter()
        .find(|(n, _)| *n == text)
        .map(|(_, s)| *s)
        .or_else(|| text.parse::<u16>().ok().filter(|_| text.bytes().all(|b| b.is_ascii_digit())))
}

impl Op {
    /// Operations with effects beyond writing their variables.
    pub fn is_impure(self) -> bool {
        matches!(
            self,
            Op::Call
                | Op::CallUntyped
                | Op::Tailcall
                | Op::TailcallUntyped
                | Op::Syscall
                | Op::SyscallUntyped
                | Op::Store
                | Op::StoreStruct
                | Op::Intrinsic
                | Op::IntrinsicSsa
                | Op::MemoryIntrinsicSsa
                | Op::Jump
                | Op::JumpTo
                | Op::Ret
                | Op::Noret
                | Op::If
                | Op::Goto
                | Op::Bp
                | Op::Trap
                | Op::Unimpl
                | Op::UnimplMem
                | Op::Undef
        )
    }

    /// Operand `index` of this operation is a memory address.  Binary Ninja sizes the
    /// address expression inside a structure access by the access width, so two
    /// spellings of one address may differ in size and mean the same thing.
    pub fn is_address_operand(self, index: usize) -> bool {
        index == 0 && matches!(self, Op::Load | Op::LoadStruct | Op::Store | Op::StoreStruct)
    }

    /// A field operation, and whether its base operand is a pointer to the object
    /// (`true`) or the variable holding it (`false`).
    pub fn field_base_is_pointer(self) -> Option<bool> {
        match self {
            Op::LoadStruct | Op::StoreStruct => Some(true),
            Op::VarField | Op::SetVarField | Op::AddressOfField => Some(false),
            _ => None,
        }
    }

    /// The plain memory operation a field operation is spelled as when its
    /// object sits at a constant address (a global): `[&g + 0x17].b` for
    /// `load_struct.b(&g, 0x17)`.
    pub fn flat_field_op(self) -> Option<Op> {
        match self {
            Op::LoadStruct | Op::VarField => Some(Op::Load),
            Op::StoreStruct | Op::SetVarField => Some(Op::Store),
            _ => None,
        }
    }

    /// Operations whose integer operand may carry a symbol.
    pub fn is_symbol_op(self) -> bool {
        matches!(self, Op::ConstPtr | Op::Import | Op::ExternPtr | Op::Const)
    }

    pub fn is_const_op(self) -> bool {
        matches!(self, Op::Const | Op::ConstPtr)
    }

    pub fn is_pointer_op(self) -> bool {
        matches!(self, Op::ConstPtr | Op::Import | Op::ExternPtr)
    }

    pub fn is_call_like(self) -> bool {
        matches!(
            self,
            Op::Call | Op::CallUntyped | Op::Tailcall | Op::TailcallUntyped | Op::Syscall | Op::SyscallUntyped
        )
    }

    /// The comparison with the opposite truth value.
    pub fn complement(self) -> Option<Op> {
        Some(match self {
            Op::CmpE => Op::CmpNe,
            Op::CmpNe => Op::CmpE,
            Op::CmpSlt => Op::CmpSge,
            Op::CmpSge => Op::CmpSlt,
            Op::CmpSle => Op::CmpSgt,
            Op::CmpSgt => Op::CmpSle,
            Op::CmpUlt => Op::CmpUge,
            Op::CmpUge => Op::CmpUlt,
            Op::CmpUle => Op::CmpUgt,
            Op::CmpUgt => Op::CmpUle,
            _ => return None,
        })
    }

    /// The canonical comparison a fact is recorded with (`a != b` is `a == b` negated).
    pub fn canonical_cmp(self) -> Option<Op> {
        Some(match self {
            Op::CmpNe => Op::CmpE,
            Op::CmpSge => Op::CmpSlt,
            Op::CmpSgt => Op::CmpSle,
            Op::CmpUge => Op::CmpUlt,
            Op::CmpUgt => Op::CmpUle,
            _ => return None,
        })
    }

    /// Operations that end a basic block.
    pub fn is_terminator(self) -> bool {
        matches!(
            self,
            Op::If
                | Op::Goto
                | Op::Ret
                | Op::Noret
                | Op::Jump
                | Op::JumpTo
                | Op::Tailcall
                | Op::TailcallUntyped
                | Op::Trap
                | Op::Bp
        )
    }

    /// Instructions no expression site can live in.
    pub fn no_site(self) -> bool {
        matches!(
            self,
            Op::Goto | Op::Nop | Op::Noret | Op::Bp | Op::Trap | Op::Undef | Op::Unimpl | Op::JumpTo
        )
    }

    /// Arithmetic that may be widened to pointer width inside an address.
    pub fn is_pointer_arith(self) -> bool {
        matches!(
            self,
            Op::Add | Op::Sub | Op::And | Op::Or | Op::Xor | Op::Mul | Op::Lsl | Op::Neg | Op::Not
        )
    }

    /// Operations the pattern language may write in the generic `name.size(args)` form.
    pub fn is_pattern_op(self) -> bool {
        let v = self as u16;
        v <= Op::FcmpUo as u16 || v >= Op::BlockToExpand as u16
    }

    /// The infix spelling the renderer uses for binary operations.
    pub fn infix(self) -> Option<&'static str> {
        Some(match self {
            Op::Add => "+",
            Op::Sub => "-",
            Op::Mul => "*",
            Op::Divu => "u/",
            Op::Divs => "s/",
            Op::Modu => "u%",
            Op::Mods => "s%",
            Op::And => "&",
            Op::Or => "|",
            Op::Xor => "^",
            Op::Lsl => "<<",
            Op::Lsr => ">>",
            Op::Asr => "s>>",
            Op::CmpE => "==",
            Op::CmpNe => "!=",
            Op::CmpSlt => "s<",
            Op::CmpUlt => "u<",
            Op::CmpSle => "s<=",
            Op::CmpUle => "u<=",
            Op::CmpSgt => "s>",
            Op::CmpUgt => "u>",
            Op::CmpSge => "s>=",
            Op::CmpUge => "u>=",
            _ => return None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_round_trip() {
        for v in 0..Op::COUNT as u32 {
            let op = Op::from_u32(v).unwrap();
            assert_eq!(Op::from_name(op.name()), Some(op));
            assert_eq!(Op::from_name(op.short_name()), Some(op));
        }
        assert_eq!(Op::from_name("set_var".to_uppercase().as_str()), Some(Op::SetVar));
        assert_eq!(Op::SetVar.layout(), &[OperandKind::Var, OperandKind::Expr]);
        assert_eq!(Op::Call.layout(), &[OperandKind::ExprList, OperandKind::Expr, OperandKind::ExprList]);
        assert!(Op::Assert.is_pattern_op());
        assert!(!Op::SetVarSsa.is_pattern_op());
        assert!(Op::Abs.is_pattern_op());
    }
}
