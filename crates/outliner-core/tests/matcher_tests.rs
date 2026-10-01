//! The matcher: plain shapes, hoisting, rewrite rules, expression sites and
//! rendering.

mod common;

use common::*;
use outliner_core::hybrid::{normalize_condition, Node};
use outliner_core::render::render_function;

fn env() -> FakeEnv {
    FakeEnv::default()
}

// --------------------------------------------------------------------------- MatcherTests

#[test]
fn diamond_match() {
    let p = compiled(c_str_pattern(), &["s"], true, false);
    let (f, s, r) = make_c_str_func(Some("struct std::string*"), false);
    let env = env();
    let round = Round::new(&f, &env);
    let patterns = [p];
    let matches = find_matches(&round, &patterns, &[], None);
    assert_eq!(matches.len(), 1);
    let m = &matches[0];
    assert_eq!(m.entry_index, 0);
    assert_eq!(deleted(m), vec![0, 1, 2, 3]);
    assert_eq!(m.internal_blocks, vec![1, 3]);
    assert_eq!(m.exit_index, Some(4));
    assert!(m.exit_goto);
    let labels: Vec<(String, u32)> = patterns[0].labels.iter().enumerate().map(|(i, l)| (l.clone(), m.labels[i].unwrap())).collect();
    assert_eq!(labels, vec![("long".to_string(), 1), ("short".to_string(), 3), ("done".to_string(), 4)]);
    assert_eq!(binding(m, &patterns[0], "s").kind_name(), "expr");
    assert_eq!(var_of(&f, m, &patterns[0], "s"), s);
    assert_eq!(m.ret_var(&f), Some(r));
    assert_eq!(m.ret_size, 8);
}

#[test]
fn diamond_rejects_external_predecessor() {
    let p = compiled(c_str_pattern(), &["s"], true, false);
    let (f, _, _) = make_c_str_func(Some("struct std::string*"), true);
    let env = env();
    let round = Round::new(&f, &env);
    assert!(find_matches(&round, &[p], &[], None).is_empty());
}

#[test]
fn type_constraint() {
    let p = compiled(c_str_pattern(), &["s"], true, false);
    let (f, _, _) = make_c_str_func(Some("int64_t"), false); // same name, different type
    let env = env();
    let round = Round::new(&f, &env);
    assert!(find_matches(&round, &[p], &[], None).is_empty());
    let unconstrained = compiled(&c_str_pattern().replace("$s : struct std::string*", ""), &["s"], true, false);
    assert_eq!(find_matches(&round, &[unconstrained], &[], None).len(), 1);
}

#[test]
fn sequence_multiple_matches_and_exit() {
    let p = compiled("$ret = [$p + 8].q\n$ret = $ret + 1", &["p"], true, false);
    let fx = Fx::new();
    let [a, b, x, y] = ["a", "b", "x", "y"].map(|n| fx.var(n));
    let f = fx.func(vec![(
        vec![
            fx.set_var(x, fx.load(8, fx.add(fx.v(a), fx.c(8)))),
            fx.set_var(x, fx.add(fx.v(x), fx.c(1))),
            fx.set_var(y, fx.load(8, fx.add(fx.v(b), fx.c(8)))),
            fx.set_var(y, fx.add(fx.v(y), fx.c(1))),
            fx.ret(&[fx.v(x), fx.v(y)]),
        ],
        vec![],
    )]);
    let env = env();
    let round = Round::new(&f, &env);
    let patterns = [p];
    let matches = find_matches(&round, &patterns, &[], None);
    let summary: Vec<(u32, Vec<u32>, Option<u32>, bool)> = matches.iter().map(|m| (m.entry_index, deleted(m), m.exit_index, m.exit_goto)).collect();
    assert_eq!(summary, vec![(0, vec![0, 1], Some(2), false), (2, vec![2, 3], Some(4), false)]);
    assert_eq!(var_of(&f, &matches[0], &patterns[0], "p"), a);
    assert_eq!(var_of(&f, &matches[1], &patterns[0], "p"), b);
}

#[test]
fn placeholder_consistency() {
    let p = compiled("$ret = [$p].q + [$p].q", &["p"], true, false);
    let same = {
        let fx = Fx::new();
        let [a, x] = ["a", "x"].map(|n| fx.var(n));
        fx.func(vec![(vec![fx.set_var(x, fx.add(fx.load(8, fx.v(a)), fx.load(8, fx.v(a))))], vec![])])
    };
    let diff = {
        let fx = Fx::new();
        let [a, b, x] = ["a", "b", "x"].map(|n| fx.var(n));
        fx.func(vec![(vec![fx.set_var(x, fx.add(fx.load(8, fx.v(a)), fx.load(8, fx.v(b))))], vec![])])
    };
    let env = env();
    assert_eq!(find_matches(&Round::new(&same, &env), &[p.clone()], &[], None).len(), 1);
    assert!(find_matches(&Round::new(&diff, &env), &[p], &[], None).is_empty());
}

#[test]
fn temporary_live_after_region_is_rejected() {
    let p = compiled("$t = [$p].q\n$ret = $t + 1", &["p"], true, false);
    let dead = {
        let fx = Fx::new();
        let [a, t, x] = ["a", "t", "x"].map(|n| fx.var(n));
        fx.func(vec![(vec![fx.set_var(t, fx.load(8, fx.v(a))), fx.set_var(x, fx.add(fx.v(t), fx.c(1))), fx.ret(&[fx.v(x)])], vec![])])
    };
    let live = {
        let fx = Fx::new();
        let [a, t, x] = ["a", "t", "x"].map(|n| fx.var(n));
        fx.func(vec![(vec![fx.set_var(t, fx.load(8, fx.v(a))), fx.set_var(x, fx.add(fx.v(t), fx.c(1))), fx.ret(&[fx.v(x), fx.v(t)])], vec![])])
    };
    let env = env();
    assert_eq!(find_matches(&Round::new(&dead, &env), &[p.clone()], &[], None).len(), 1);
    assert!(find_matches(&Round::new(&live, &env), &[p], &[], None).is_empty());
}

#[test]
fn argument_must_not_depend_on_region_writes() {
    let p = compiled("$p = $p + 1\n$ret = [$p].q", &["p"], true, false);
    let f = {
        let fx = Fx::new();
        let [a, x] = ["a", "x"].map(|n| fx.var(n));
        fx.func(vec![(vec![fx.set_var(a, fx.add(fx.v(a), fx.c(1))), fx.set_var(x, fx.load(8, fx.v(a)))], vec![])])
    };
    let env = env();
    assert!(find_matches(&Round::new(&f, &env), &[p], &[], None).is_empty());
    // But writing the result variable itself while reading it as an argument is fine.
    let p2 = compiled("$ret = $n + 1", &["n"], true, false);
    let f2 = {
        let fx = Fx::new();
        let n = fx.var("n");
        fx.func(vec![(vec![fx.set_var(n, fx.add(fx.v(n), fx.c(1)))], vec![])])
    };
    assert_eq!(find_matches(&Round::new(&f2, &env), &[p2], &[], None).len(), 1);
}

#[test]
fn goto_fallthrough_and_explicit() {
    let p = compiled("if ($c) then a else b\na:\n$ret = 1\ngoto j\nb:\n$ret = 2\ngoto j\nj:\n", &["c"], true, false);
    let fx = Fx::new();
    let [c, r] = ["c", "r"].map(|n| fx.var(n));
    // Block 1 ends with explicit goto, block 2 falls through.
    let f = fx.func(vec![
        (vec![fx.if_(fx.v(c), 1, 3)], vec![(T, 1), (FB, 2)]),
        (vec![fx.set_var(r, fx.c(1)), fx.goto(4)], vec![(U, 3)]),
        (vec![fx.set_var(r, fx.c(2))], vec![(U, 3)]),
        (vec![fx.ret(&[fx.v(r)])], vec![]),
    ]);
    let env = env();
    let round = Round::new(&f, &env);
    let m = find_matches(&round, &[p], &[], None);
    assert_eq!(m.len(), 1);
    assert_eq!(deleted(&m[0]), vec![0, 1, 2, 3]);
    assert_eq!(m[0].exit_index, Some(4));
}

#[test]
fn call_with_symbol_and_wildcards() {
    let p = compiled("$ret = call(memcmp, $a, $b, _)\n$ret = $ret == 0", &["a", "b"], true, false);
    let fx = Fx::new();
    let [a, b, x] = ["a", "b", "x"].map(|n| fx.var(n));
    let f = fx.func(vec![(
        vec![
            fx.call(&[x], fx.cptr(0x4000), &[fx.v(a), fx.v(b), fx.c(4)]),
            fx.set_var(x, fx.cmp(Op::CmpE, fx.v(x), fx.c(0))),
        ],
        vec![],
    )]);
    let env = env_symbols(&[(0x4000, &["memcmp", "_memcmp"])], &[]);
    assert_eq!(find_matches(&Round::new(&f, &env), &[p.clone()], &[], None).len(), 1);
    let wrong = env_symbols(&[(0x4000, &["strlen"])], &[]);
    assert!(find_matches(&Round::new(&f, &wrong), &[p], &[], None).is_empty());
}

#[test]
fn const_size_masking_and_var_operand() {
    let p = compiled("$ret = var_field($v, 4) + -1", &["v"], true, false);
    let fx = Fx::new();
    let [v, x] = ["v", "x"].map(|n| fx.var(n));
    let f = fx.func(vec![(vec![fx.set_var(x, fx.bin(Op::Add, fx.var_field(v, 4, 4), fx.cs(0xFFFFFFFF, 4), 4))], vec![])]);
    let env = env();
    let round = Round::new(&f, &env);
    let patterns = [p];
    let m = find_matches(&round, &patterns, &[], None);
    assert_eq!(m.len(), 1);
    assert_eq!(binding(&m[0], &patterns[0], "v").kind_name(), "var");
}

#[test]
fn match_pattern_at_offset_in_block() {
    let p = compiled("$ret = [$p].q", &["p"], true, false);
    let fx = Fx::new();
    let [a, x, y] = ["a", "x", "y"].map(|n| fx.var(n));
    let f = fx.func(vec![(vec![fx.set_var(y, fx.c(1)), fx.set_var(x, fx.load(8, fx.v(a)))], vec![])]);
    let env = env();
    let round = Round::new(&f, &env);
    let patterns = [p];
    assert!(match_pattern_at(&round, &patterns, 0, 0, &no_instrs(), &no_vars(), &[]).is_none());
    assert!(match_pattern_at(&round, &patterns, 0, 1, &no_instrs(), &no_vars(), &[]).is_some());
}

// --------------------------------------------------------------------------- HoistingTests

#[test]
fn data_and_size_through_hoisted_loads() {
    let c = make_checksum_func();
    let f = &c.f;
    let data = compiled(DATA_PATTERN, &["s"], true, false);
    let size = compiled(SIZE_PATTERN, &["s"], true, false);
    let env = env();
    let round = Round::new(f, &env);
    let patterns = [data, size];
    let matches = find_matches(&round, &patterns, &rules(), None);
    assert_eq!(matches.len(), 2);
    let (m_data, m_size) = (&matches[0], &matches[1]);
    // data(): the flag definition (2) is shared with size() and stays; x10's load (3) goes.
    assert_eq!(m_data.call_index, 5);
    assert_eq!(m_data.entry_index, 5);
    assert_eq!(deleted(m_data), vec![3, 5, 6, 7, 8, 9]);
    assert_eq!(m_data.internal_blocks, vec![6, 8]);
    assert_eq!((m_data.exit_index, m_data.exit_goto), (Some(10), true));
    assert_eq!(var_of(f, m_data, &patterns[0], "s"), c.s); // through the copy x8 = s
    assert_eq!(m_data.ret_var(f), Some(c.d));
    assert_eq!(sorted(m_data.chased.iter().map(|(d, _)| *d).collect()), vec![0, 2, 3]);
    // size(): x11's load (4) goes, the flag definition (2) now has no uses left and goes
    // too, and so does the copy x8 = s (0) once nothing reads x8 any more.
    assert_eq!(m_size.call_index, 10);
    assert_eq!(deleted(m_size), vec![0, 2, 4, 10, 11, 12, 13, 14]);
    // followed definitions in the entry block do not make it the match's own block
    assert!(m_size.region_blocks.contains(&0));
    assert_eq!(m_size.own_blocks, vec![10, 11, 13]);
    assert_eq!(var_of(f, m_size, &patterns[1], "s"), c.s);
    assert_eq!(m_size.ret_var(f), Some(c.sz));
}

#[test]
fn flag_kept_when_it_is_an_argument_elsewhere() {
    let c = make_checksum_func();
    // A first pattern that passes the flag variable itself as an argument
    let flag_pat = compiled(
        "if ($flag s< 0) then a else b\na:\n$ret = load_struct.q($s, 0)\ngoto j\nb:\n$ret = $s\ngoto j\nj:\n",
        &["s", "flag"],
        true,
        false,
    );
    let size = compiled(SIZE_PATTERN, &["s"], true, false);
    let env = env();
    let round = Round::new(&c.f, &env);
    let matches = find_matches(&round, &[flag_pat, size], &[], None);
    assert_eq!(matches.len(), 2);
    assert!(!matches[1].deleted.contains(2)); // __s_1 is live as the first call's argument
}

#[test]
fn kept_instruction_interference() {
    let p = compiled("$t = [$p].q\n$ret = $t + 1", &["p"], true, false);
    let env = env();
    let ok = {
        let fx = Fx::new();
        let [a, t, x, u] = ["a", "t", "x", "u"].map(|n| fx.var(n));
        fx.func(vec![(
            vec![fx.set_var(t, fx.load(8, fx.v(a))), fx.set_var(u, fx.c(5)), fx.set_var(x, fx.add(fx.v(t), fx.c(1))), fx.ret(&[fx.v(x), fx.v(u)])],
            vec![],
        )])
    };
    let m = find_matches(&Round::new(&ok, &env), &[p.clone()], &[], None);
    assert_eq!(m.len(), 1);
    assert_eq!((m[0].entry_index, m[0].call_index, m[0].kept.clone()), (0, 2, vec![1]));
    // kept instruction writes the argument -> reject
    let bad1 = {
        let fx = Fx::new();
        let [a, t, x] = ["a", "t", "x"].map(|n| fx.var(n));
        fx.func(vec![(
            vec![fx.set_var(t, fx.load(8, fx.v(a))), fx.set_var(a, fx.c(5)), fx.set_var(x, fx.add(fx.v(t), fx.c(1))), fx.ret(&[fx.v(x), fx.v(a)])],
            vec![],
        )])
    };
    assert!(find_matches(&Round::new(&bad1, &env), &[p.clone()], &[], None).is_empty());
    // kept instruction reads a temporary the pattern defines -> reject
    let bad2 = {
        let fx = Fx::new();
        let [a, t, x, u] = ["a", "t", "x", "u"].map(|n| fx.var(n));
        fx.func(vec![(
            vec![fx.set_var(t, fx.load(8, fx.v(a))), fx.set_var(u, fx.v(t)), fx.set_var(x, fx.add(fx.v(t), fx.c(1))), fx.ret(&[fx.v(x), fx.v(u)])],
            vec![],
        )])
    };
    assert!(find_matches(&Round::new(&bad2, &env), &[p.clone()], &[], None).is_empty());
    // kept instruction with side effects -> reject
    let bad3 = {
        let fx = Fx::new();
        let [a, t, x] = ["a", "t", "x"].map(|n| fx.var(n));
        fx.func(vec![(
            vec![fx.set_var(t, fx.load(8, fx.v(a))), fx.store(8, fx.v(a), fx.c(0)), fx.set_var(x, fx.add(fx.v(t), fx.c(1))), fx.ret(&[fx.v(x)])],
            vec![],
        )])
    };
    assert!(find_matches(&Round::new(&bad3, &env), &[p], &[], None).is_empty());
}

#[test]
fn chase_rejects_ambiguous_and_reused_definitions() {
    let p = compiled("$ret = [$p].q + 1", &["p"], true, false);
    let env = env();
    // t defined by a call, not a set_var: no chase
    let f1 = {
        let fx = Fx::new();
        let [t, x] = ["t", "x"].map(|n| fx.var(n));
        fx.func(vec![(vec![fx.call(&[t], fx.cptr(0x4000), &[]), fx.set_var(x, fx.add(fx.v(t), fx.c(1)))], vec![])])
    };
    assert!(find_matches(&Round::new(&f1, &env), &[p.clone()], &[], None).is_empty());
    // chased definition still used elsewhere: kept, match still fine
    let fx = Fx::new();
    let [a, t, x] = ["a", "t", "x"].map(|n| fx.var(n));
    let f2 = fx.func(vec![(vec![fx.set_var(t, fx.load(8, fx.v(a))), fx.set_var(x, fx.add(fx.v(t), fx.c(1))), fx.ret(&[fx.v(x), fx.v(t)])], vec![])]);
    let m = find_matches(&Round::new(&f2, &env), &[p], &[], None);
    assert_eq!(m.len(), 1);
    assert_eq!(deleted(&m[0]), vec![1]);
    assert_eq!(m[0].chased, vec![(0, t)]);
}

#[test]
fn generic_statement() {
    let p = compiled("set_var_field.q($d, 8, $v)\n$ret = $v", &["v"], true, false);
    let fx = Fx::new();
    let [d, v, x] = ["d", "v", "x"].map(|n| fx.var(n));
    let f = fx.func(vec![(vec![fx.set_var_field(d, 8, fx.v(v), 8), fx.set_var(x, fx.v(v))], vec![])]);
    assert!(matches!(p.blocks[0].stmts[0], Stmt::Expr(_)));
    let env = env();
    let round = Round::new(&f, &env);
    let patterns = [p];
    let m = find_matches(&round, &patterns, &[], None);
    assert_eq!(m.len(), 1);
    assert!(matches!(binding(&m[0], &patterns[0], "d"), Binding::Var(x) if *x == d));
}

// --------------------------------------------------------------------------- RenderTests

#[test]
fn render_round_trip() {
    let (f, _, _) = make_c_str_func(None, false);
    let text = render_function(&f, None, None, None);
    assert!(text.contains("if ((sx.q([($s + 0x17)].b) s< 0x0)) then L1 else L3"), "{text}");
    assert!(text.contains("L1:"));
    assert!(text.contains("$r = [$s].q"));
    assert!(text.contains("goto L4"));
    // The rendering parses back and matches the function it came from.
    let pattern_text: Vec<&str> = text.lines().filter(|l| !l.trim_start().starts_with("return")).collect();
    let pattern_text = pattern_text.join("\n").replace("$r =", "$ret =");
    let p = compiled(&pattern_text, &["s"], true, false);
    let env = env();
    assert_eq!(find_matches(&Round::new(&f, &env), &[p], &[], None).len(), 1);
}

#[test]
fn render_noret() {
    let fx = Fx::new();
    let f = fx.func(vec![(vec![fx.call(&[], fx.cptr(0x5010), &[]), fx.noret()], vec![])]);
    let text = render_function(&f, None, None, None);
    assert!(text.contains("noret()"));
}

#[test]
fn render_misc() {
    let fx = Fx::new();
    let [a, x] = ["a", "x b"].map(|n| fx.var(n));
    let f = fx.func(vec![(
        vec![
            fx.call(&[x], fx.cptr(0x4000), &[fx.v(a), fx.c(-3)]),
            fx.store(1, fx.v(a), fx.low_part(1, fx.var_field(x, 0, 4))),
            fx.set_var_field(a, 8, fx.v(x), 8),
            fx.ret(&[]),
        ],
        vec![],
    )]);
    let symbols = |addr: u64| if addr == 0x4000 { vec!["memcmp".to_string()] } else { vec![] };
    let text = render_function(&f, Some(&symbols), None, None);
    assert!(text.contains("$x_b = call(\"memcmp\", $a, -0x3)"), "{text}");
    assert!(text.contains("[$a].b = low_part.b(var_field.d($x_b, 0x0))"), "{text}");
    assert!(text.contains("set_var_field.q($a, 0x8, $x_b)"), "{text}");
    assert!(text.contains("    return    #"), "{text}");
}

// --------------------------------------------------------------------------- RuleTests

#[test]
fn guard_spellings_match_one_pattern() {
    // Every spelling of the flag test the compiler produced matches the single
    // guard `sx(load_struct.b($s, 0x17)) s< 0` once the rules are available.
    let fx = Fx::new();
    let s = fx.var("s");
    let [t, u] = ["t", "u"].map(|n| fx.var(n));
    let b = |fx: &Fx| fx.load_struct(1, fx.v(s), 0x17);
    let forms = [
        fx.cmp(Op::CmpSlt, fx.sx(8, b(&fx)), fx.c(0)),                                                        // plain
        fx.bin(Op::CmpSlt, fx.var_field(t, 0, 4), fx.cs(0, 4), 4),                                            // t = sx.q(b)
        fx.bin(Op::CmpSlt, fx.sx(4, fx.low_part(1, fx.var_field(u, 0, 4))), fx.cs(0, 4), 4),                  // u = zx.q(b)
        fx.bin(Op::CmpNe, fx.and(fx.sx(4, b(&fx)), fx.cs(0x80000000, 4), 4), fx.cs(0, 4), 4),
        fx.bin(Op::CmpNe, fx.and(fx.var_field(u, 0, 4), fx.cs(0x80, 4), 4), fx.cs(0, 4), 4),
        fx.bin(Op::CmpNe, fx.and(fx.sx(8, b(&fx)), fx.c(-0x8000000000000000), 8), fx.c(0), 8),
    ];
    let mut instrs = vec![fx.set_var(t, fx.sx(8, b(&fx))), fx.set_var(u, fx.zx(8, b(&fx)))];
    for form in &forms {
        instrs.push(fx.if_(*form, 3, 3));
    }
    let f = fx.func(vec![(instrs, vec![])]);
    let pattern = parse_pattern(PURE_DATA).unwrap();
    let guard = pattern.guarded_value().unwrap().guard.clone();
    let env = env();
    let round = Round::new(&f, &env);
    for (k, form) in forms.iter().enumerate() {
        let index = 2 + k as u32;
        let node = Node::Expr(*form);
        if k > 0 {
            assert!(match_expression(&round, &pattern, &guard, &node, index, &[], Vec::new()).is_none());
        }
        let bound = match_expression(&round, &pattern, &guard, &node, index, &rules(), Vec::new()).unwrap_or_else(|| panic!("form {k}"));
        let b = bound[pattern.ph("s").unwrap().0 as usize].as_ref().unwrap();
        assert_eq!(bound_var(&f, b), s, "form {k}");
    }
}

#[test]
fn when_rule_needs_the_fact() {
    let fx = Fx::new();
    let s = fx.var("s");
    let x = fx.var("x");
    let b = fx.load_struct(1, fx.v(s), 0x17);
    let f = fx.func(vec![(vec![fx.set_vars(x, fx.sx(4, b), 4)], vec![])]);
    let pattern = parse_pattern(PURE_SIZE).unwrap();
    let short_arm = pattern.guarded_value().unwrap().false_arm.clone(); // zx(load_struct.b($s, 0x17))
    let site = Node::Expr(operand(&f, 0, 1)); // sx.d(load_struct.b(s, 0x17))
    let env = env();
    let round = Round::new(&f, &env);
    assert!(match_expression(&round, &pattern, &short_arm, &site, 0, &rules(), Vec::new()).is_none());
    let guard = Node::rn(Op::CmpSlt, None, vec![Node::rn(Op::Sx, None, vec![Node::Expr(b)]), Node::Const(0)]);
    let facts = vec![normalize_condition(&f, &guard, false)]; // the sign bit is known clear
    let bound = match_expression(&round, &pattern, &short_arm, &site, 0, &rules(), facts).unwrap();
    assert_eq!(bound_var(&f, bound[pattern.ph("s").unwrap().0 as usize].as_ref().unwrap()), s);
    let wrong = vec![normalize_condition(&f, &guard, true)]; // known set: sx and zx differ
    assert!(match_expression(&round, &pattern, &short_arm, &site, 0, &rules(), wrong).is_none());
}

#[test]
fn diamonds_with_rules() {
    let c = make_checksum_func();
    let data = compiled(PURE_DATA, &["s"], true, true);
    let size = compiled(PURE_SIZE, &["s"], true, true);
    let env = env();
    let round = Round::new(&c.f, &env);
    let patterns = [data, size];
    // size's guard is `var_field.d(__s_1, 0) s< 0` and its short arm is `sx.q(b)`:
    // neither matches the single size pattern without the rules.
    assert_eq!(find_matches(&round, &patterns, &[], None).len(), 1);
    let matches = find_matches(&round, &patterns, &rules(), None);
    let calls: Vec<u32> = matches.iter().map(|m| m.call_index).collect();
    assert_eq!(calls, vec![5, 10]);
    assert_eq!(var_of(&c.f, &matches[1], &patterns[1], "s"), c.s);
}

#[test]
fn inverted_branch() {
    let fx = Fx::new();
    let [s, r] = ["s", "r"].map(|n| fx.var(n));
    // if (sx(b) s>= 0) then short else long: the compiler flipped the test
    let f = fx.func(vec![
        (vec![fx.if_(fx.cmp(Op::CmpSge, fx.sx(8, fx.load_struct(1, fx.v(s), 0x17)), fx.c(0)), 1, 3)], vec![(T, 1), (FB, 2)]),
        (vec![fx.set_var(r, fx.v(s)), fx.goto(5)], vec![(U, 3)]),                         // 1,2 short
        (vec![fx.set_var(r, fx.load_struct(8, fx.v(s), 0)), fx.goto(5)], vec![(U, 3)]),   // 3,4 long
        (vec![fx.ret(&[fx.v(r)])], vec![]),
    ]);
    let data = compiled(PURE_DATA, &["s"], true, true);
    let env = env();
    let round = Round::new(&f, &env);
    let patterns = [data];
    let m = find_matches(&round, &patterns, &[], None);
    assert_eq!(m.len(), 1);
    let labels: Vec<(&str, u32)> = patterns[0].labels.iter().enumerate().map(|(i, l)| (l.as_str(), m[0].labels[i].unwrap())).collect();
    assert_eq!(labels, vec![("long", 3), ("short", 1), ("done", 5)]);
}

// --------------------------------------------------------------------------- ValuePatternTests

fn syms() -> Vec<(u64, &'static [&'static str])> {
    vec![(SIZE_ADDR, &["size"]), (DATA_ADDR, &["data"])]
}

#[test]
fn empty_inside_condition() {
    let fx = Fx::new();
    let [s, n] = ["s", "size_1"].map(|nm| fx.var(nm));
    let f = fx.func(vec![
        (vec![fx.call(&[n], fx.cptr(SIZE_ADDR as i64), &[fx.v(s)]), fx.if_(fx.cmp(Op::CmpE, fx.v(n), fx.c(0)), 2, 3)], vec![(T, 1), (FB, 2)]),
        (vec![fx.ret(&[fx.c(1)])], vec![]),
        (vec![fx.ret(&[fx.c(0)])], vec![]),
    ]);
    let empty = compiled_s(EMPTY_PATTERN, true);
    let env = env_symbols(&syms(), &[SIZE_ADDR]);
    let round = Round::new(&f, &env);
    let patterns = [empty.clone()];
    let sites = find_expression_sites(&round, &patterns, &[], None, &no_instrs(), &no_vars());
    assert_eq!(sites.len(), 1);
    let site = &sites[0];
    assert_eq!((site.instr_index, site.whole_rhs), (1, false));
    assert_eq!(site.expr, operand(&f, 1, 0));
    assert_eq!(bound_var(&f, site.binding(patterns[0].ph("s").unwrap()).unwrap()), s);
    assert_eq!(site.deleted_sorted(), vec![0]); // the size() call only fed this site
    assert_eq!(site.chased, vec![(0, n)]);
    // not pure: the call cannot be made again inside empty(), so there is no site
    let impure = env_symbols(&syms(), &[]);
    assert!(find_expression_sites(&Round::new(&f, &impure), &patterns, &[], None, &no_instrs(), &no_vars()).is_empty());
    // the pattern itself must be pure to be hoisted
    let not_pure = [compiled_s(EMPTY_PATTERN, false)];
    assert!(find_expression_sites(&round, &not_pure, &[], None, &no_instrs(), &no_vars()).is_empty());
}

#[test]
fn whole_rhs_and_nested_sites() {
    let fx = Fx::new();
    let [s, d, d_1, n, x, y] = ["s", "d", "d_1", "n", "x", "y"].map(|nm| fx.var(nm));
    let f = fx.func(vec![(
        vec![
            fx.call(&[d], fx.cptr(DATA_ADDR as i64), &[fx.v(s)]),                                           // 0
            fx.set_vars(x, fx.load(1, fx.v(d)), 1),                                                         // 1  x = [d].b
            fx.call(&[d_1], fx.cptr(DATA_ADDR as i64), &[fx.v(s)]),                                         // 2
            fx.call(&[n], fx.cptr(SIZE_ADDR as i64), &[fx.v(s)]),                                           // 3
            fx.set_vars(y, fx.zx(4, fx.load(1, fx.sub(fx.add(fx.v(d_1), fx.v(n)), fx.c(1)))), 4),           // 4  y = zx.d([d_1 + n - 1].b)
            fx.ret(&[fx.v(x), fx.v(y)]),
        ],
        vec![],
    )]);
    let patterns = [compiled_s(FRONT_PATTERN, true), compiled_s(BACK_PATTERN, true)];
    let env = env_symbols(&syms(), &[SIZE_ADDR, DATA_ADDR]);
    let round = Round::new(&f, &env);
    let sites = find_expression_sites(&round, &patterns, &[], None, &no_instrs(), &no_vars());
    let summary: Vec<(u32, bool)> = sites.iter().map(|t| (t.instr_index, t.whole_rhs)).collect();
    assert_eq!(summary, vec![(1, true), (4, false)]);
    assert_eq!(sites[0].dest, Some(x));
    assert_eq!(sites[0].size, 1);
    assert_eq!(sites[0].deleted_sorted(), vec![0]);
    assert_eq!(sites[1].expr, sub(&f, operand(&f, 4, 1), 0));
    assert_eq!(sites[1].deleted_sorted(), vec![2, 3]); // both calls are consumed
    // back's site is inside zx.d(...): the load, not the zero-extension
    assert_eq!(f.op(sub(&f, operand(&f, 4, 1), 0)), Op::Load);
}

#[test]
fn shared_call_result_is_not_consumed() {
    // data() made once and read by front() and back(): outlining either would
    // show two data() calls, so neither is a site; likewise one size() feeding
    // two empty() tests, or an empty() test next to another use of the size.
    let env = env_symbols(&syms(), &[SIZE_ADDR, DATA_ADDR]);
    let front = compiled_s(FRONT_PATTERN, true);
    let back = compiled_s(BACK_PATTERN, true);
    let empty = compiled_s(EMPTY_PATTERN, true);
    let f = {
        let fx = Fx::new();
        let [s, d, n, x, y] = ["s", "d", "n", "x", "y"].map(|nm| fx.var(nm));
        fx.func(vec![(
            vec![
                fx.call(&[d], fx.cptr(DATA_ADDR as i64), &[fx.v(s)]),
                fx.call(&[n], fx.cptr(SIZE_ADDR as i64), &[fx.v(s)]),
                fx.set_vars(x, fx.load(1, fx.v(d)), 1),
                fx.set_vars(y, fx.zx(4, fx.load(1, fx.sub(fx.add(fx.v(d), fx.v(n)), fx.c(1)))), 4),
                fx.ret(&[fx.v(x), fx.v(y)]),
            ],
            vec![],
        )])
    };
    assert!(find_expression_sites(&Round::new(&f, &env), &[front, back], &[], None, &no_instrs(), &no_vars()).is_empty());
    let f = {
        let fx = Fx::new();
        let [s, n, x, y] = ["s", "n", "x", "y"].map(|nm| fx.var(nm));
        fx.func(vec![(
            vec![
                fx.call(&[n], fx.cptr(SIZE_ADDR as i64), &[fx.v(s)]),
                fx.set_vars(x, fx.un(Op::BoolToInt, 1, fx.cmp(Op::CmpE, fx.v(n), fx.c(0))), 1),
                fx.set_vars(y, fx.un(Op::BoolToInt, 1, fx.cmp(Op::CmpE, fx.v(n), fx.c(0))), 1),
                fx.ret(&[fx.v(x), fx.v(y)]),
            ],
            vec![],
        )])
    };
    assert!(find_expression_sites(&Round::new(&f, &env), &[empty.clone()], &[], None, &no_instrs(), &no_vars()).is_empty());
    let f = {
        let fx = Fx::new();
        let [s, n, x, z] = ["s", "n", "x", "z"].map(|nm| fx.var(nm));
        fx.func(vec![(
            vec![
                fx.call(&[n], fx.cptr(SIZE_ADDR as i64), &[fx.v(s)]),
                fx.set_vars(x, fx.un(Op::BoolToInt, 1, fx.cmp(Op::CmpE, fx.v(n), fx.c(0))), 1),
                fx.set_var(z, fx.add(fx.v(n), fx.c(1))),
                fx.ret(&[fx.v(x), fx.v(z)]),
            ],
            vec![],
        )])
    };
    assert!(find_expression_sites(&Round::new(&f, &env), &[empty], &[], None, &no_instrs(), &no_vars()).is_empty());
}

#[test]
fn back_matches_add_negative_one() {
    // Compilers spell `p - 1` as `p + -1`; the example rule folds that back.
    let fx = Fx::new();
    let [s, d, n, t, y] = ["s", "d", "n", "t", "y"].map(|nm| fx.var(nm));
    let f = fx.func(vec![(
        vec![
            fx.call(&[d], fx.cptr(DATA_ADDR as i64), &[fx.v(s)]),                          // 0
            fx.call(&[n], fx.cptr(SIZE_ADDR as i64), &[fx.v(s)]),                          // 1
            fx.set_var(t, fx.add(fx.v(d), fx.v(n))),                                       // 2
            fx.set_vars(y, fx.zx(4, fx.load(1, fx.add(fx.v(t), fx.c(-1)))), 4),            // 3  y = zx.d([t + -1].b)
            fx.ret(&[fx.v(y)]),
        ],
        vec![],
    )]);
    let patterns = [compiled_s(BACK_PATTERN, true)];
    let env = env_symbols(&syms(), &[SIZE_ADDR, DATA_ADDR]);
    let round = Round::new(&f, &env);
    assert!(find_expression_sites(&round, &patterns, &[], None, &no_instrs(), &no_vars()).is_empty());
    let sites = find_expression_sites(&round, &patterns, &rules(), None, &no_instrs(), &no_vars());
    let summary: Vec<(u32, bool)> = sites.iter().map(|t| (t.instr_index, t.whole_rhs)).collect();
    assert_eq!(summary, vec![(3, false)]);
    assert_eq!(sites[0].expr, sub(&f, operand(&f, 3, 1), 0));
    assert_eq!(sites[0].deleted_sorted(), vec![0, 1, 2]);
    assert_eq!(bound_var(&f, sites[0].binding(patterns[0].ph("s").unwrap()).unwrap()), s);
}

#[test]
fn argument_overwritten_before_site_is_rejected() {
    let fx = Fx::new();
    let [s, d, x] = ["s", "d", "x"].map(|nm| fx.var(nm));
    let f = fx.func(vec![(
        vec![
            fx.call(&[d], fx.cptr(DATA_ADDR as i64), &[fx.v(s)]),   // 0
            fx.set_var(s, fx.c(0)),                                  // 1  s changes before the site
            fx.set_vars(x, fx.load(1, fx.v(d)), 1),                  // 2
            fx.ret(&[fx.v(x)]),
        ],
        vec![],
    )]);
    let env = env_symbols(&syms(), &[DATA_ADDR]);
    let sites = find_expression_sites(&Round::new(&f, &env), &[compiled_s(FRONT_PATTERN, true)], &[], None, &no_instrs(), &no_vars());
    assert!(sites.is_empty());
}

// --------------------------------------------------------------------------- IntrinsicTests

#[test]
fn render_intrinsic() {
    let fx = Fx::new();
    let [a, lo, hi] = ["a", "lo", "hi"].map(|n| fx.var(n));
    let f = fx.func(vec![(
        vec![
            fx.intrinsic(&[lo, hi], "_umul128", &[fx.v(a), fx.c(3)]),
            fx.intrinsic(&[], "__dmb", &[fx.c(0xb)]),
            fx.ret(&[fx.v(hi)]),
        ],
        vec![],
    )]);
    let text = render_function(&f, None, None, None);
    assert!(text.contains("$lo, $hi = intrinsic(\"_umul128\", $a, 0x3)"), "{text}");
    assert!(text.contains("    intrinsic(\"__dmb\", 0xb)"), "{text}");
    assert!(!text.contains("unsupported"), "{text}");
}

#[test]
fn intrinsic_statement_matches() {
    // The rendering of an intrinsic parses back as a pattern statement that
    // matches the instruction: outputs bind, the name compares (wildcards
    // allowed), the arguments match, and a wrong name or arity fails.
    let l = from_pattern_text(
        "
            $lo, $hi = intrinsic(\"_umul128\", $a, $b)
            intrinsic(\"__dmb\", 0xb)
            $r = $hi + 1
            return $r
        ",
        &[],
    )
    .unwrap();
    let f = &l.func;
    assert!(render_function(f, None, None, None).contains("$lo, $hi = intrinsic(\"_umul128\", $a, $b)"));
    let env = FakeEnv::default();
    let round = Round::new(f, &env);
    let good = compiled("_, $ret = intrinsic(\"_umul128\", $a, $b)\nintrinsic(\"__dmb\", 0xb)\n", &["a", "b"], true, false);
    let matches = find_matches(&round, &[good], &[], None);
    assert_eq!(matches.len(), 1);
    assert_eq!(matches[0].ret_var(f), Some(l.var("hi")));
    assert_eq!(matches[0].deleted_sorted(), vec![0, 1]);
    let glob = compiled("_, $ret = intrinsic(\"_umul*\", $a, ...)\n", &["a"], true, false);
    assert_eq!(find_matches(&round, &[glob], &[], None).len(), 1);
    let extra = compiled("$ret, ... = intrinsic(\"_umul128\", $a, $b)\n", &["a", "b"], true, false);
    assert_eq!(find_matches(&round, &[extra], &[], None).len(), 1);
    let wrong = [
        ("_, $ret = intrinsic(\"_mul128\", $a, $b)\n", &["a", "b"][..]), // another name
        ("_, $ret = intrinsic(\"_umul128\", $a)\n", &["a"][..]),         // fewer arguments
        ("$ret = intrinsic(\"_umul128\", $a, $b)\n", &["a", "b"][..]),   // fewer outputs
    ];
    for (text, params) in wrong {
        let p = compiled(text, params, true, false);
        assert!(find_matches(&round, &[p], &[], None).is_empty(), "{text}");
    }
}

// --------------------------------------------------------------------------- ArgumentTests

#[test]
fn argument_written_before_the_call_is_rejected() {
    // A matched statement that overwrites an argument variable before the
    // call site would make the call read the wrong value.
    let fx = Fx::new();
    let s = fx.tvar("s", STRING_T);
    let r = fx.var("r");
    let f = fx.func(vec![
        (
            vec![
                fx.set_var(s, fx.add(fx.v(s), fx.c(8))),                                                                // 0
                fx.if_(fx.cmp(Op::CmpSlt, fx.sx(8, fx.load_struct(1, fx.v(s), 0x17)), fx.c(0)), 2, 4),                  // 1
            ],
            vec![(T, 1), (FB, 2)],
        ),
        (vec![fx.set_var(r, fx.load_struct(8, fx.v(s), 0)), fx.goto(6)], vec![(U, 3)]), // 2, 3
        (vec![fx.set_var(r, fx.v(s)), fx.goto(6)], vec![(U, 3)]),                       // 4, 5
        (vec![fx.ret(&[fx.v(r)])], vec![]),                                             // 6
    ]);
    let body = PURE_DATA.split_once("__pure").unwrap().1;
    let shifted = compiled(&format!("$s = $s + 8\n{body}"), &["s"], true, true);
    let env = FakeEnv::default();
    assert!(find_matches(&Round::new(&f, &env), &[shifted], &[], None).is_empty());
    let data = compiled(PURE_DATA, &["s"], true, true);
    let entries: Vec<u32> = find_matches(&Round::new(&f, &env), &[data], &[], None).iter().map(|m| m.entry_index).collect();
    assert_eq!(entries, vec![1]);
}

#[test]
fn a_copy_of_a_bound_variable_is_followed_only_as_far_as_it() {
    // `$ret` stands for `x`, itself a copy of the load; the comparison reads a
    // second copy, `t = x`.  Following `t` back must stop at `x` rather than at
    // the load's `a`, and the copy goes with the match.
    let l = from_pattern_text(
        "
    $a = [$p].d
    $x = $a
    $t = $x
    $c = $t != 1
    return $x, $c
",
        &[("p", "int32_t*")],
    )
    .unwrap();
    let pattern = compiled(
        "signature: int f(int* p)\nresult: $c = call(f, $p) != 1\n$old = [$p].d\n$ret = $old\n$c = $ret != 1\n",
        &["p"],
        true,
        false,
    );
    let env = FakeEnv::default();
    let matches = find_matches(&Round::new(&l.func, &env), &[pattern], &[], None);
    assert_eq!(matches.len(), 1);
    assert_eq!(matches[0].ret_var(&l.func), Some(l.var("x")));
    assert_eq!(deleted(&matches[0]), vec![0, 1, 2, 3]);
}
