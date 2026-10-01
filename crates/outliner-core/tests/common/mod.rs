//! Shared helpers for the integration tests: fixtures, the shared rule chunk,
//! and accessors over matches.
#![allow(dead_code)]

pub use outliner_core::binding::Binding;
pub use outliner_core::fake::{from_pattern_text, intern_type, FakeEnv, Fx, Loaded, Structs, FB, T, U};
pub use outliner_core::fused::{compute_dominators, find_fused_matches, FusedMatch};
pub use outliner_core::il::{BlockSet, BranchKind, ExprId, Function, InstrSet, VarId};
pub use outliner_core::matcher::{find_matches, match_expression, match_pattern_at, no_instrs, no_vars, Match, Round, VarSet};
pub use outliner_core::ops::Op;
pub use outliner_core::pattern::{parse_pattern, split_chunks, Expr, Pattern, PhId, Rule, Stmt, RET};
pub use outliner_core::sites::{find_expression_sites, ExprSite};

pub const SIZE_ADDR: u64 = 0x4010;
pub const DATA_ADDR: u64 = 0x4000;
pub const MEMCMP_ADDR: u64 = 0x5000;
pub const THROW_ADDR: u64 = 0x5010;
pub const PRINTF_ADDR: u64 = 0x5020;
pub const EMPTY_ADDR: u64 = 0x5030;
pub const MEMCHR_ADDR: u64 = 0x5040;
pub const RFIND_ADDR: u64 = 0x5050;
pub const NEW_ADDR: u64 = 0x5060;
pub const LENGTH_THROW_ADDR: u64 = 0x5070;
pub const MEMMOVE_ADDR: u64 = 0x5080;
pub const FIND_ADDR: u64 = 0x5090;
pub const COPY_EXT_ADDR: u64 = 0x50a0;
pub const SUBSTR_ADDR: u64 = 0x50b0;
pub const SINK_ADDR: u64 = 0x50c0;
pub const DELETE_ADDR: u64 = 0x50d0;

pub const STRING_T: &str = "std::__1::string const&";
pub const COPY_EXT_NAME: &str = "std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char> >::__init_copy_ctor_external[abi:nqe210106]";

pub const DATA: &str = "std::string::data";
pub const SIZE: &str = "std::string::size";
pub const CAPACITY: &str = "std::string::capacity";
pub const COMPARE: &str = "std::string::compare";
pub const FIND: &str = "std::string::find";
pub const CTOR: &str = "std::string::string";
pub const EMPTY: &str = "std::string::empty";
pub const RFIND: &str = "std::string::rfind";
pub const SUBSTR: &str = "std::string::substr";
pub const DTOR: &str = "std::string::~string";

pub const RULES: &str = "
rules: libc++ string idioms
rewrite: (and.d(sx.d($b), 0x80000000)) != 0                 =>  sx($b) s< 0
rewrite: (and.q(sx.q($b), 0x8000000000000000)) != 0         =>  sx($b) s< 0
rewrite: (and.d(var_field.d(zx.q($b), 0), 0x80)) != 0        =>  sx($b) s< 0
rewrite: var_field.d(sx.q($b), 0) s< 0                       =>  sx($b) s< 0
rewrite: sx.d(low_part.b(var_field.d(zx.q($b), 0))) s< 0     =>  sx($b) s< 0
rewrite: var_field.d(sx.q($b), 0)                            =>  sx.d($b)
rewrite: sx($b) => zx($b) when sx($b) s>= 0
rewrite: load_struct.b($p, 0) => [$p].b
rewrite: $a + -1 => $a - 1
";

pub const PURE_DATA: &str = "
signature: char const* data(struct S* s) __pure
if (sx(load_struct.b($s, 0x17)) s< 0) then long else short
long:
    $ret = load_struct.q($s, 0)
    goto done
short:
    $ret = $s
    goto done
done:
";

pub const PURE_SIZE: &str = "
signature: uint64_t size(struct S* s) __pure
if (sx(load_struct.b($s, 0x17)) s< 0) then long else short
long:
    $ret = load_struct.q($s, 8)
    goto done
short:
    $ret = zx(load_struct.b($s, 0x17))
    goto done
done:
";

pub const EMPTY_PATTERN: &str = "
signature: bool empty(struct S* s) __pure
value: call(size, $s) == 0
";
pub const FRONT_PATTERN: &str = "
signature: char front(struct S* s) __pure
value: [call(data, $s)].b
";
pub const BACK_PATTERN: &str = "
signature: char back(struct S* s) __pure
value: [call(data, $s) + call(size, $s) - 1].b
";

pub fn params(names: &[&str]) -> Vec<String> {
    names.iter().map(|s| s.to_string()).collect()
}

/// A pattern validated against a signature the way the plugin would.
pub fn compiled(text: &str, param_names: &[&str], returns: bool, pure: bool) -> Pattern {
    let mut p = parse_pattern(text).unwrap_or_else(|e| panic!("{e}\n{text}"));
    p.validate_signature(&params(param_names), returns, pure, None).unwrap_or_else(|e| panic!("{e}\n{text}"));
    p
}

/// A pattern compiled for the parameter `s` returning a value.
pub fn compiled_s(text: &str, pure: bool) -> Pattern {
    compiled(text, &["s"], true, pure)
}

pub fn rules() -> Vec<Rule> {
    parse_pattern(RULES).unwrap().rules
}

pub fn by_name<'a>(patterns: &'a [Pattern], name: &str) -> Vec<&'a Pattern> {
    patterns.iter().filter(|p| p.name == name).collect()
}

pub fn select(patterns: &[Pattern], keep: impl Fn(&Pattern) -> bool) -> Vec<Pattern> {
    patterns.iter().filter(|p| keep(p)).cloned().collect()
}

/// The variable a binding reads: the variable itself, or the one an `MLIL_VAR` expression reads.
pub fn bound_var(f: &Function, b: &Binding) -> VarId {
    b.bound_var(f).unwrap_or_else(|| panic!("not a variable binding: {b:?}"))
}

pub fn const_of(f: &Function, b: &Binding) -> i128 {
    b.const_value(f).unwrap_or_else(|| panic!("not a constant binding: {b:?}"))
}

/// A match's binding of the placeholder `name`.
pub fn binding<'m>(m: &'m Match, p: &Pattern, name: &str) -> &'m Binding {
    m.binding(p.ph(name).unwrap_or_else(|| panic!("no placeholder ${name}"))).unwrap_or_else(|| panic!("${name} unbound"))
}

pub fn var_of(f: &Function, m: &Match, p: &Pattern, name: &str) -> VarId {
    bound_var(f, binding(m, p, name))
}

pub fn deleted(m: &Match) -> Vec<u32> {
    m.deleted_sorted()
}

pub fn range(a: u32, b: u32) -> Vec<u32> {
    (a..b).collect()
}

pub fn sorted(mut v: Vec<u32>) -> Vec<u32> {
    v.sort_unstable();
    v.dedup();
    v
}

/// The operand of `f.instr(i)` at position `k` (an expression).
pub fn operand(f: &Function, i: u32, k: usize) -> ExprId {
    f.sub(f.instr(i), k).unwrap()
}

pub fn sub(f: &Function, e: ExprId, k: usize) -> ExprId {
    f.sub(e, k).unwrap()
}

pub fn env_symbols(symbols: &[(u64, &[&str])], pure: &[u64]) -> FakeEnv {
    FakeEnv::with(symbols, pure)
}

pub fn c_str_pattern() -> &'static str {
    "
# libc++ std::string::c_str() on arm64
signature: char const* c_str(struct std::string* s)
$s : struct std::string*

if (sx.q([$s + 0x17].b) s< 0) then long else short
long:
    $ret = [$s].q
    goto done
short:
    $ret = $s
    goto done
done:
"
}

/// 0: if (sx.q([s+0x17].b) s< 0) then 1 else 3
/// 1: r = [s].q ; 2: goto 4
/// 3: r = s            (falls through)
/// 4: return r
pub fn make_c_str_func(s_type: Option<&str>, extra_pred: bool) -> (Function, VarId, VarId) {
    let fx = Fx::new();
    let s = match s_type {
        Some(t) => fx.tvar("s", t),
        None => fx.var("s"),
    };
    let r = fx.tvar("r", "char const*");
    let mut blocks = vec![
        (vec![fx.if_(fx.cmp(Op::CmpSlt, fx.sx(8, fx.load(1, fx.add(fx.v(s), fx.c(0x17)))), fx.c(0)), 1, 3)], vec![(T, 1), (FB, 2)]),
        (vec![fx.set_var(r, fx.load(8, fx.v(s))), fx.goto(4)], vec![(U, 3)]),
        (vec![fx.set_var(r, fx.v(s))], vec![(U, 3)]),
        (vec![fx.ret(&[fx.v(r)])], vec![]),
    ];
    if extra_pred {
        // Add a block that also jumps into the "long" block from outside.
        blocks.push((vec![fx.goto(1)], vec![(U, 1)]));
    }
    (fx.func(blocks), s, r)
}

pub struct Checksum {
    pub f: Function,
    pub s: VarId,
    pub x8: VarId,
    pub res: VarId,
    pub s1: VarId,
    pub x10: VarId,
    pub x11: VarId,
    pub d: VarId,
    pub sz: VarId,
}

/// Shape of libc++ data()/size() as Binary Ninja shows it for a `checksum` function:
/// loads hoisted above the branch, the flag byte shared by both inlined calls.
pub fn make_checksum_func() -> Checksum {
    let fx = Fx::new();
    let [s, x8, res, s1, x10, x11, d, sz] = ["s", "x8", "result", "__s_1", "x10", "x11", "__s", "__s_2"].map(|n| fx.var(n));
    let f = fx.func(vec![
        (
            vec![
                fx.set_var(x8, fx.v(s)),                                           // 0
                fx.set_vars(res, fx.cs(-0x7ee3623b, 4), 4),                        // 1
                fx.set_var(s1, fx.sx(8, fx.load_struct(1, fx.v(x8), 0x17))),       // 2
                fx.set_var(x10, fx.load_struct(8, fx.v(x8), 0)),                   // 3
                fx.set_var(x11, fx.load_struct(8, fx.v(x8), 8)),                   // 4
                fx.if_(fx.cmp(Op::CmpSlt, fx.v(s1), fx.c(0)), 6, 8),               // 5
            ],
            vec![(T, 1), (FB, 2)],
        ),
        (vec![fx.set_var(d, fx.v(x10)), fx.goto(10)], vec![(U, 3)]),  // 6,7
        (vec![fx.set_var(d, fx.v(x8)), fx.goto(10)], vec![(U, 3)]),   // 8,9
        (vec![fx.if_(fx.bin(Op::CmpSlt, fx.var_field(s1, 0, 4), fx.cs(0, 4), 4), 11, 13)], vec![(T, 4), (FB, 5)]), // 10
        (vec![fx.set_var(sz, fx.v(x11)), fx.goto(15)], vec![(U, 6)]),  // 11,12
        (vec![fx.set_var(sz, fx.v(s1)), fx.goto(15)], vec![(U, 6)]),   // 13,14
        (vec![fx.ret(&[fx.v(d), fx.v(sz), fx.v(res)])], vec![]),       // 15
    ]);
    Checksum { f, s, x8, res, s1, x10, x11, d, sz }
}

pub const DATA_PATTERN: &str = "
signature: char const* data(struct S* s)
if (sx(load_struct.b($s, 0x17)) s< 0) then long else short
long:
    $ret = load_struct.q($s, 0)
    goto done
short:
    $ret = $s
    goto done
done:
";

pub const SIZE_PATTERN: &str = "
signature: uint64_t size(struct S* s)
if (var_field.d(sx(load_struct.b($s, 0x17)), 0) s< 0) then long else short
long:
    $ret = load_struct.q($s, 8)
    goto done
short:
    $ret = sx(load_struct.b($s, 0x17))
    goto done
done:
";

pub struct CstrOr {
    pub f: Function,
    pub s: VarId,
    pub fb: VarId,
    pub fl: VarId,
    pub x9: VarId,
    pub x8: VarId,
    pub r1: VarId,
    pub r0: VarId,
}

/// cstr_or as Binary Ninja shows it: empty() and c_str() fused under one flag test,
/// with the ternary and the return duplicated into both arms.
pub fn make_cstr_or_func(impure_false_arm: bool) -> CstrOr {
    let fx = Fx::new();
    let [s, fb, fl, x9, x8, r1, r0] = ["s", "fallback", "__s", "x9", "x8", "x0_1", "x0"].map(|n| fx.var(n));
    let mut false_arm = Vec::new();
    if impure_false_arm {
        false_arm.push(fx.store(8, fx.v(s), fx.c(0)));
    }
    false_arm.push(fx.if_(fx.bin(Op::CmpE, fx.vs(fl, 4), fx.cs(0, 4), 4), 10, 12));
    let f = fx.func(vec![
        (
            vec![
                fx.set_vars(fl, fx.sx(4, fx.load_struct(1, fx.v(s), 0x17)), 4),                                             // 0
                fx.if_(fx.bin(Op::CmpNe, fx.and(fx.vs(fl, 4), fx.cs(0x80000000, 4), 4), fx.cs(0, 4), 4), 2, 5),               // 1
            ],
            vec![(T, 1), (FB, 2)],
        ),
        (
            vec![
                fx.set_var(x9, fx.load_struct(8, fx.v(s), 0)),          // 2
                fx.set_var(x8, fx.load_struct(8, fx.v(s), 8)),          // 3
                fx.if_(fx.cmp(Op::CmpE, fx.v(x8), fx.c(0)), 6, 8),      // 4
            ],
            vec![(T, 3), (FB, 4)],
        ),
        (false_arm, vec![(T, 5), (FB, 6)]),                                          // 5 (+extra)
        (vec![fx.set_var(r1, fx.v(fb)), fx.goto(14)], vec![(U, 7)]),                 // 6,7
        (vec![fx.set_var(r1, fx.v(x9)), fx.goto(14)], vec![(U, 7)]),                 // 8,9
        (vec![fx.set_var(r0, fx.v(fb)), fx.goto(15)], vec![(U, 8)]),                 // 10,11
        (vec![fx.set_var(r0, fx.v(s)), fx.goto(15)], vec![(U, 8)]),                  // 12,13
        (vec![fx.ret(&[fx.v(r1)])], vec![]),                                         // 14
        (vec![fx.ret(&[fx.v(r0)])], vec![]),                                         // 15
    ]);
    CstrOr { f, s, fb, fl, x9, x8, r1, r0 }
}

pub struct IsBracketed {
    pub f: Function,
    pub s: VarId,
    pub fl: VarId,
    pub x8_1: VarId,
    pub x10_1: VarId,
}

/// is_bracketed as Binary Ninja shows it: empty(), front() and back() fused
/// under one flag test; the long arm reassigns s and __s in place, one branch is
/// inverted, and the values merge at the join (block 14).
pub fn make_is_bracketed_func() -> IsBracketed {
    let fx = Fx::new();
    let [s, fl, x0_2, x0, x8_1, x10_1, x8_2, x8_3, x8_4, x0_1] =
        ["s", "__s", "x0_2", "x0", "x8_1", "x10_1", "x8_2", "x8_3", "x8_4", "x0_1"].map(|n| fx.var(n));
    let f = fx.func(vec![
        (
            vec![
                fx.set_var(fl, fx.sx(8, fx.load_struct(1, fx.v(s), 0x17))),                                                   // 0
                fx.if_(fx.bin(Op::CmpNe, fx.and(fx.v(fl), fx.c(-0x8000000000000000), 8), fx.c(0), 8), 2, 4),                    // 1
            ],
            vec![(T, 1), (FB, 2)],
        ),
        (vec![fx.set_var(fl, fx.load_struct(8, fx.v(s), 8)), fx.if_(fx.cmp(Op::CmpE, fx.v(fl), fx.c(0)), 5, 7)], vec![(T, 3), (FB, 4)]), // 2,3
        (vec![fx.if_(fx.bin(Op::CmpE, fx.var_field(fl, 0, 4), fx.cs(0, 4), 4), 10, 12)], vec![(T, 5), (FB, 6)]),          // 4
        (vec![fx.set_var(x0_2, fx.c(0)), fx.ret(&[fx.c(0)])], vec![]),                                                     // 5,6
        (
            vec![
                fx.set_var(s, fx.load_struct(8, fx.v(s), 0)),                                      // 7
                fx.set_vars(x8_1, fx.zx(4, fx.load_struct(1, fx.v(s), 0)), 4),                     // 8
                fx.if_(fx.bin(Op::CmpNe, fx.vs(x8_1, 4), fx.cs(0x5b, 4), 4), 5, 14),               // 9
            ],
            vec![(T, 3), (FB, 7)],
        ),
        (vec![fx.set_var(x0, fx.c(0)), fx.ret(&[fx.c(0)])], vec![]),                                                       // 10,11
        (
            vec![
                fx.set_vars(x10_1, fx.zx(4, fx.load_struct(1, fx.v(s), 0)), 4),                    // 12
                fx.if_(fx.bin(Op::CmpE, fx.vs(x10_1, 4), fx.cs(0x5b, 4), 4), 14, 10),              // 13
            ],
            vec![(T, 7), (FB, 5)],
        ),
        (
            vec![
                fx.set_var(x8_2, fx.add(fx.v(s), fx.v(fl))),                                                            // 14
                fx.set_vars(x8_3, fx.zx(4, fx.load(1, fx.sub(fx.v(x8_2), fx.c(1)))), 4),                                 // 15
                fx.set_vars(x8_4, fx.un(Op::BoolToInt, 1, fx.bin(Op::CmpE, fx.vs(x8_3, 4), fx.cs(0x5d, 4), 4)), 1),     // 16
                fx.set_vars(x0_1, fx.vs(x8_4, 1), 1),                                                                   // 17
                fx.ret(&[fx.vs(x0_1, 1)]),                                                                              // 18
            ],
            vec![],
        ),
    ]);
    IsBracketed { f, s, fl, x8_1, x10_1 }
}

/// `(flag.w & 0x80) != 0`: the sign-bit test as Binary Ninja spells it here.
pub fn flag_test(fx: &Fx, flag_var: VarId) -> ExprId {
    fx.bin(Op::CmpNe, fx.and(fx.var_field(flag_var, 0, 4), fx.cs(0x80, 4), 4), fx.cs(0, 4), 4)
}

pub fn sso_store(fx: &Fx, var: VarId, offset: i64, value: ExprId, size: u16) -> ExprId {
    fx.set_var_field(var, offset, value, size)
}

/// The names of the patterns that produced each match, in order.
pub fn names(matches: &[Match], patterns: &[Pattern]) -> Vec<String> {
    matches.iter().map(|m| patterns[m.pattern].name.clone()).collect()
}

/// A block set over block starts.
pub fn blocks_at(f: &Function, starts: &[u32]) -> BlockSet {
    let mut set = f.block_set();
    for s in starts {
        set.insert(f.block_at(*s).unwrap().id.0 as usize);
    }
    set
}

/// `claimed` blocks for the fused pass as the workflow computes them: own and internal blocks.
pub fn claimed_blocks(f: &Function, matches: &[Match]) -> BlockSet {
    let mut set = f.block_set();
    for m in matches {
        for s in m.own_blocks.iter().chain(&m.internal_blocks) {
            set.insert(f.block_at(*s).unwrap().id.0 as usize);
        }
    }
    set
}

pub fn deleted_union(f: &Function, matches: &[Match]) -> InstrSet {
    let mut set = f.instr_set();
    for m in matches {
        set.union_with(&m.deleted);
    }
    set
}

pub fn live_union(f: &Function, matches: &[Match], patterns: &[Pattern]) -> VarSet {
    outliner_core::matcher::arg_var_set(f, matches, patterns)
}
