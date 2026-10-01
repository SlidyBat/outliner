//! What a placeholder stands for once matched.

use std::rc::Rc;

use smallvec::SmallVec;

use crate::il::{ExprId, Function, TypeId, VarId};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum MemberKind {
    /// The variable holding the object: the placeholder stands for the member itself.
    Var,
    /// A variable holding a pointer to the object.
    Ptr,
    /// The variable whose address that pointer is.
    Addr,
    /// A pointer expression.
    Expr,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum MemberBase {
    Var(VarId),
    Expr(ExprId),
}

/// A string that is a member of a bigger object.  For every kind but `Var`
/// the placeholder stands for a pointer to the member.
#[derive(Clone, Debug)]
pub struct MemberRef {
    pub kind: MemberKind,
    pub base: MemberBase,
    pub offset: i64,
    pub ty: Option<TypeId>,
}

impl MemberRef {
    pub fn new(kind: MemberKind, base: MemberBase, offset: i64, ty: Option<TypeId>) -> MemberRef {
        MemberRef { kind, base, offset, ty }
    }

    pub fn pointer(&self) -> bool {
        self.kind != MemberKind::Var
    }

    pub fn base_var(&self) -> Option<VarId> {
        match self.base {
            MemberBase::Var(v) => Some(v),
            MemberBase::Expr(_) => None,
        }
    }

    /// The same member of the same object.
    pub fn same(&self, other: &MemberRef, f: &Function) -> bool {
        self.kind == other.kind && self.offset == other.offset && self.same_base(other.kind, other.base, f)
    }

    /// The same object, addressed the same way.
    pub fn same_base(&self, kind: MemberKind, base: MemberBase, f: &Function) -> bool {
        if kind != self.kind {
            return false;
        }
        match (self.base, base) {
            (MemberBase::Expr(a), MemberBase::Expr(b)) => f.expr_equal(a, b, false),
            (a, b) => a == b,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Binding {
    Var(VarId),
    /// An expression; `address`: it is a load/store address (sizes are meaningless).
    Expr { expr: ExprId, address: bool },
    /// A constant the matcher computed or the code spelled; `origin`: where the
    /// binary holds it, when the code loaded it from there.
    Int { value: i128, origin: Option<u64> },
    /// The characters of a byte image, packed little-endian (any length).
    Bytes { bytes: Rc<[u8]>, origin: Option<u64> },
    /// The address of a variable (`&s`).
    Addr(VarId),
    Member(MemberRef),
    /// An object at a fixed address (a global, or a member of one), which the
    /// code reaches through constant pointers.  `object`: the placeholder
    /// stands for the object itself (a pattern written for a variable holding
    /// it, whose `&$s` is the address); otherwise for a pointer to it.
    Global { addr: u64, object: bool },
}

impl Binding {
    pub fn kind_name(&self) -> &'static str {
        match self {
            Binding::Var(_) => "var",
            Binding::Expr { .. } => "expr",
            Binding::Int { .. } | Binding::Bytes { .. } => "int",
            Binding::Addr(_) => "addr",
            Binding::Member(_) => "member",
            Binding::Global { .. } => "global",
        }
    }

    pub fn is_address_expr(&self) -> bool {
        matches!(self, Binding::Expr { address: true, .. })
    }

    /// The variable the binding stands for, if it is (a read of) one.
    pub fn bound_var(&self, f: &Function) -> Option<VarId> {
        match self {
            Binding::Var(v) => Some(*v),
            Binding::Expr { expr, .. } => f.var_of(*expr),
            _ => None,
        }
    }

    /// The variable a call writing through this binding (re)defines, if any:
    /// the variable itself, or the object a member belongs to.
    pub fn redefined_var(&self) -> Option<VarId> {
        match self {
            Binding::Var(v) => Some(*v),
            Binding::Member(m) if m.kind == MemberKind::Var => m.base_var(),
            _ => None,
        }
    }

    /// The variables a call argument bound this way depends on: the variable,
    /// the variables of the expression, or, for an address, the variable whose
    /// address is passed (the call reads its contents).
    pub fn reads(&self, f: &Function) -> SmallVec<[VarId; 4]> {
        match self {
            Binding::Var(v) | Binding::Addr(v) => SmallVec::from_slice(&[*v]),
            Binding::Expr { expr, .. } => f.vars_read(*expr),
            Binding::Member(m) => match m.base {
                MemberBase::Var(v) => SmallVec::from_slice(&[v]),
                MemberBase::Expr(e) => f.vars_read(e),
            },
            _ => SmallVec::new(),
        }
    }

    /// The constant the binding stands for, whether the matcher computed it or
    /// the code spelled it.
    pub fn const_value(&self, f: &Function) -> Option<i128> {
        match self {
            Binding::Int { value, .. } => Some(*value),
            Binding::Bytes { bytes, .. } => bytes_to_i128(bytes),
            Binding::Expr { expr, .. } => f.const_value(*expr).map(|v| v as i128),
            _ => None,
        }
    }

    pub fn origin(&self) -> Option<u64> {
        match self {
            Binding::Int { origin, .. } | Binding::Bytes { origin, .. } => *origin,
            _ => None,
        }
    }

    /// Two bindings of the same placeholder denote the same thing.
    pub fn same(&self, other: &Binding, f: &Function) -> bool {
        match (self, other) {
            (Binding::Var(a), Binding::Var(b)) | (Binding::Addr(a), Binding::Addr(b)) => a == b,
            (Binding::Expr { expr: a, address: aa }, Binding::Expr { expr: b, address: ab }) => {
                f.expr_equal(*a, *b, *aa || *ab)
            }
            (Binding::Int { value: a, .. }, Binding::Int { value: b, .. }) => a == b,
            (Binding::Bytes { bytes: a, .. }, Binding::Bytes { bytes: b, .. }) => a == b,
            (Binding::Int { .. }, Binding::Bytes { .. }) | (Binding::Bytes { .. }, Binding::Int { .. }) => {
                self.const_value(f).is_some() && self.const_value(f) == other.const_value(f)
            }
            (Binding::Member(a), Binding::Member(b)) => a.same(b, f),
            (Binding::Global { addr: a, object: oa }, Binding::Global { addr: b, object: ob }) => a == b && oa == ob,
            // a pointer to a global, and the code's own spelling of that address
            (Binding::Global { addr, object: false }, Binding::Expr { expr, .. })
            | (Binding::Expr { expr, .. }, Binding::Global { addr, object: false }) => f.const_value(*expr) == Some(*addr as i64),
            _ => false,
        }
    }
}

/// Up to sixteen little-endian bytes as an integer.
pub fn bytes_to_i128(bytes: &[u8]) -> Option<i128> {
    if bytes.len() > 16 {
        return None;
    }
    let mut buf = [0u8; 16];
    buf[..bytes.len()].copy_from_slice(bytes);
    Some(i128::from_le_bytes(buf))
}
