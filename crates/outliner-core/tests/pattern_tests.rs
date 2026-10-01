//! The pattern language.

use outliner_core::ops::Op;
use outliner_core::pattern::{negate, parse_pattern, Dest, Expr, PatternError, Stmt, RET};

const C_STR_PATTERN: &str = "
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
";

fn assert_err(result: Result<impl std::fmt::Debug, PatternError>, fragment: &str) {
    match result {
        Err(e) => assert!(e.0.contains(fragment), "expected {fragment:?} in {:?}", e.0),
        Ok(v) => panic!("expected an error mentioning {fragment:?}, got {v:?}"),
    }
}

fn params(names: &[&str]) -> Vec<String> {
    names.iter().map(|s| s.to_string()).collect()
}

#[test]
fn diamond_pattern_structure() {
    let p = parse_pattern(C_STR_PATTERN).unwrap();
    assert_eq!(p.signature.as_deref(), Some("char const* c_str(struct std::string* s)"));
    let s = p.ph("s").unwrap();
    assert_eq!(p.type_of(s).unwrap().text, "struct std::string*");
    let labels: Vec<Option<&str>> = p.blocks.iter().map(|b| b.label.map(|l| p.label_name(l))).collect();
    assert_eq!(labels, vec![None, Some("long"), Some("short"), Some("done")]);
    let entry = &p.blocks[0].stmts;
    assert_eq!(entry.len(), 1);
    let Stmt::If { cond, .. } = &entry[0] else { panic!() };
    let cond = cond.as_op().unwrap();
    assert_eq!(cond.op, Op::CmpSlt);
    let sx = cond.args[0].as_op().unwrap();
    assert_eq!((sx.op, sx.size), (Op::Sx, Some(8)));
    let ld = sx.args[0].as_op().unwrap();
    assert_eq!((ld.op, ld.size), (Op::Load, Some(1)));
    let add = ld.args[0].as_op().unwrap();
    assert_eq!(add.op, Op::Add);
    assert_eq!(add.args, vec![Expr::Placeholder(s), Expr::Const(0x17)]);
    assert_eq!(cond.args[1], Expr::Const(0));
    assert!(matches!(p.blocks[1].stmts[0], Stmt::SetVar { .. }));
    assert!(matches!(p.blocks[1].stmts[1], Stmt::Goto(_)));
    assert!(p.blocks[3].stmts.is_empty());
    let used: Vec<&str> = p.placeholders().iter().map(|id| p.ph_name(id)).collect();
    assert_eq!(used, vec!["ret", "s"]);
    assert!(p.assigned_placeholders().contains(RET));
    assert!(!p.assigned_placeholders().contains(s));
}

#[test]
fn precedence_and_operators() {
    let p = parse_pattern("$r = $a + $b * 2 - [$c].d & 0xff").unwrap();
    let Stmt::SetVar { src, .. } = &p.blocks[0].stmts[0] else { panic!() };
    // ((a + (b*2)) - load) & 0xff
    let e = src.as_op().unwrap();
    assert_eq!(e.op, Op::And);
    assert_eq!(e.args[1], Expr::Const(0xff));
    let left = e.args[0].as_op().unwrap();
    assert_eq!(left.op, Op::Sub);
    assert_eq!(left.args[0].as_op().unwrap().op, Op::Add);
    assert_eq!(left.args[0].as_op().unwrap().args[1].as_op().unwrap().op, Op::Mul);
    let load = left.args[1].as_op().unwrap();
    assert_eq!((load.op, load.size), (Op::Load, Some(4)));
}

#[test]
fn signed_unsigned_ops_and_negatives() {
    let p = parse_pattern("$r = ($a u< $b) == ($c s>> 3); $q = -1; $z = -$a; $w = ~$a").unwrap();
    let srcs: Vec<&Expr> = p.blocks[0]
        .stmts
        .iter()
        .map(|s| match s {
            Stmt::SetVar { src, .. } => src,
            _ => panic!(),
        })
        .collect();
    assert_eq!(srcs[0].as_op().unwrap().op, Op::CmpE);
    assert_eq!(srcs[0].as_op().unwrap().args[0].as_op().unwrap().op, Op::CmpUlt);
    assert_eq!(srcs[0].as_op().unwrap().args[1].as_op().unwrap().op, Op::Asr);
    assert_eq!(srcs[1], &Expr::Const(-1));
    assert_eq!(srcs[2].as_op().unwrap().op, Op::Neg);
    assert_eq!(srcs[3].as_op().unwrap().op, Op::Not);
}

#[test]
fn generic_ops_store_call_return() {
    let p = parse_pattern(
        "
            [$p + 8].q = zx.q(low_part.b($x))
            $n = call(memcmp, $a, $b, ...)
            call(\"_free\", $a)
            _ = call($fp, $a)
            $y = mulu.dp.q($a, $b)
            $z = var_field($v, 4)
            $t = &$v
            return $n
        ",
    )
    .unwrap();
    let s = &p.blocks[0].stmts;
    let Stmt::Store { size, src, .. } = &s[0] else { panic!() };
    assert_eq!(*size, Some(8));
    let lp = src.as_op().unwrap().args[0].as_op().unwrap();
    assert_eq!((lp.op, lp.size), (Op::LowPart, Some(1)));
    let Stmt::Call(c) = &s[1] else { panic!() };
    assert!(matches!(&c.target, Expr::Symbol(sym) if sym.name == "memcmp"));
    assert!(c.variadic);
    let Stmt::Call(c) = &s[2] else { panic!() };
    assert!(matches!(&c.target, Expr::Symbol(sym) if sym.name == "_free"));
    assert!(c.outputs.is_empty());
    let Stmt::Call(c) = &s[3] else { panic!() };
    assert_eq!(c.outputs, vec![Dest::Wildcard]);
    assert_eq!(c.target, Expr::Placeholder(p.ph("fp").unwrap()));
    let Stmt::SetVar { src, .. } = &s[4] else { panic!() };
    assert_eq!((src.as_op().unwrap().op, src.as_op().unwrap().size), (Op::MuluDp, Some(8)));
    let Stmt::SetVar { src, .. } = &s[5] else { panic!() };
    assert_eq!(src.as_op().unwrap().op, Op::VarField);
    assert_eq!(src.as_op().unwrap().args, vec![Expr::Placeholder(p.ph("v").unwrap()), Expr::Const(4)]);
    let Stmt::SetVar { src, .. } = &s[6] else { panic!() };
    assert_eq!(src.as_op().unwrap().op, Op::AddressOf);
    assert!(matches!(s[7], Stmt::Ret(_)));
}

#[test]
fn errors() {
    assert_err(parse_pattern("$r = $a < 3"), "ambiguous");
    assert_err(parse_pattern("if ($a) then x else y\nx:\n$r = 1\ngoto y\n"), "undefined label");
    assert_err(parse_pattern("$r = 1\ngoto l\nl:\n$q = 2\ngoto l"), "must not end with");
    assert_err(parse_pattern("$r = 1\nl:\n$q = 2"), "must end with");
    assert_err(parse_pattern("$r = frobnicate($a)"), "unknown MLIL operation");
    assert_err(parse_pattern("l:\n$r = 1"), "never targeted");
    assert_err(parse_pattern("l:\n"), "at least one statement");
    assert_err(parse_pattern("$r = 1\ngoto b\na:\n$q = 2\ngoto b\nb:\n"), "never targeted");
}

#[test]
fn signature_validation() {
    let mut p = parse_pattern("$ret = [$s].q").unwrap();
    p.validate_signature(&params(&["s"]), true, false, None).unwrap();
    assert_eq!(p.params, params(&["s"]));
    assert_err(parse_pattern("$ret = [$s].q").unwrap().validate_signature(&params(&["s", "n"]), true, false, None), "never appears");
    assert_err(parse_pattern("$x = [$s].q").unwrap().validate_signature(&params(&["s"]), true, false, None), "never assigns");
    assert_err(parse_pattern("$ret = [$s].q").unwrap().validate_signature(&params(&["s"]), false, false, None), "returns void");
    assert_err(
        parse_pattern("$q : int\n$ret = [$s].q").unwrap().validate_signature(&params(&["s"]), true, false, None),
        "unused placeholder",
    );
}

#[test]
fn qualified_names() {
    let p = parse_pattern("value: call(std::string::size, $s) == 0").unwrap();
    let call = p.value.as_ref().unwrap().as_op().unwrap().args[0].as_call().unwrap();
    assert!(matches!(&call.target, Expr::Symbol(s) if s.name == "std::string::size"));
    let body = "$ret = call(g, $s)\n";
    for target in ["std::string::find", "\"std::string::find\""] {
        let mut p = parse_pattern(&format!("result: call({target}, $s) == -1\n{body}")).unwrap();
        p.validate_signature(&params(&["s"]), true, false, Some("std::string::find")).unwrap();
    }
    assert!(parse_pattern(&format!("result: call(std::string::size, $s) == -1\n{body}"))
        .unwrap()
        .validate_signature(&params(&["s"]), true, false, Some("std::string::find"))
        .is_err());
}

const BODY: &str = "
if (sx(load_struct.b($s, 0x17)) s< 0) then long else short
long:
    $ret = load_struct.q($s, 0)
    goto done
short:
    $ret = $s
    goto done
done:
";

#[test]
fn result_allows_specialised_parameters() {
    let mut p = parse_pattern(&format!("result: call(compare, $s, 0) == 0\n{BODY}")).unwrap();
    assert_eq!(p.result_call().unwrap().args[1], Expr::Const(0));
    p.validate_signature(&params(&["s", "pos"]), true, true, Some("compare")).unwrap();
    assert!(parse_pattern(BODY).unwrap().validate_signature(&params(&["s", "pos"]), true, false, None).is_err());
    assert!(p.clone().validate_signature(&params(&["s", "pos"]), true, false, Some("other")).is_err());
    assert!(p.clone().validate_signature(&params(&["s"]), true, false, Some("compare")).is_err());
    assert!(p.clone().validate_signature(&params(&["s", "pos"]), false, false, Some("compare")).is_err());
    assert!(parse_pattern(&format!("result: call(compare, $s, $ret) == 0\n{BODY}"))
        .unwrap()
        .validate_signature(&params(&["s", "pos"]), true, false, Some("compare"))
        .is_err());
}

#[test]
fn result_needs_one_own_call() {
    assert!(parse_pattern(&format!("result: $s == 0\n{BODY}")).is_err());
    assert!(parse_pattern(&format!("result: call(a, $s) + call(b, $s)\n{BODY}")).is_err());
    assert!(parse_pattern("result: call(a, $s)\nvalue: [$s].b").is_err());
}

#[test]
fn call_output_lists() {
    let p = parse_pattern("$a, _ = call(f, $x)\n$b, ... = call(g)\ncall(h)").unwrap();
    let Stmt::Call(a) = &p.blocks[0].stmts[0] else { panic!() };
    assert_eq!(a.outputs, vec![Dest::Ph(p.ph("a").unwrap()), Dest::Wildcard]);
    assert!(!a.extra_outputs);
    let Stmt::Call(b) = &p.blocks[0].stmts[1] else { panic!() };
    assert_eq!((b.outputs.clone(), b.extra_outputs), (vec![Dest::Ph(p.ph("b").unwrap())], true));
    let Stmt::Call(c) = &p.blocks[0].stmts[2] else { panic!() };
    assert!(c.outputs.is_empty());
    assert!(parse_pattern("$a, $b = $x + 1").is_err());
}

#[test]
fn named_result_lines() {
    let body = "$r, ... = call(memchr, call(data, $s), $c, call(size, $s))\n$ret = $r - call(data, $s)\n\
                if ($r != 0) then a else b\na:\n    $z = ($ret == -1)\n    goto done\nb:\n    $z = 1\n\
                    goto done\ndone:\n";
    let mut p = parse_pattern(&format!("result: $z = call(find, $s, $c, 0) == -1\n{body}")).unwrap();
    p.validate_signature(&params(&["s", "c", "pos"]), true, true, Some("find")).unwrap();
    let outputs: Vec<&str> = p.output_placeholders().iter().map(|id| p.ph_name(id)).collect();
    assert_eq!(outputs, vec!["ret", "z"]);
    assert!(p.ret_is_call());
    let args: Vec<&str> = p.argument_placeholders().iter().map(|id| p.ph_name(*id)).collect();
    assert_eq!(args, vec!["s", "c"]);
    let mut p = parse_pattern(&format!("result: call(find, $s, $c, 0)\nresult: $z = $ret == -1\n{body}")).unwrap();
    p.validate_signature(&params(&["s", "c", "pos"]), true, false, Some("find")).unwrap();
    assert!(parse_pattern(&format!("result: $q = call(find, $s, $c, 0) == -1\n{body}"))
        .unwrap()
        .validate_signature(&params(&["s", "c", "pos"]), true, false, Some("find"))
        .is_err());
    assert!(parse_pattern(&format!("result: call(find, $s, $c, 0)\nresult: $z = call(find, $s, $c, 1) == -1\n{body}")).is_err());
    assert!(parse_pattern(&format!("result: $z = $c == 1\n{body}")).is_err());
}

#[test]
fn void_result_with_address_argument() {
    let body = "set_var_field.b($s, 0x17, 4)\nset_var_field.d($s, 0, $chars)\nset_var_field.b($s, 4, 0)\n";
    let mut p = parse_pattern(&format!("result: call(ctor, &$s, $chars, 4)\n{body}")).unwrap();
    p.validate_signature(&params(&["s", "chars", "n"]), false, false, Some("ctor")).unwrap();
    let refs: Vec<&str> = p.reference_placeholders().iter().map(|id| p.ph_name(id)).collect();
    assert_eq!(refs, vec!["s"]);
    let args: Vec<&str> = p.argument_placeholders().iter().map(|id| p.ph_name(*id)).collect();
    assert_eq!(args, vec!["s", "chars"]);
    assert!(parse_pattern(&format!("result: call(ctor, &$s, $chars, 4) == 0\n{body}"))
        .unwrap()
        .validate_signature(&params(&["s", "chars", "n"]), false, false, Some("ctor"))
        .is_err());
    assert!(parse_pattern(&format!("result: call(ctor, &$s, $chars, $n)\n{body}"))
        .unwrap()
        .validate_signature(&params(&["s", "chars", "n"]), false, false, Some("ctor"))
        .is_err());
}

#[test]
fn branch_exit() {
    let body = "$r, ... = call(memchr, call(data, $s) + $pos, $c, call(size, $s) - $pos)\n\
                if ($r == 0) then missing else found\nfound:\n    $ret = $r - call(data, $s)\n";
    let mut p = parse_pattern(&format!("branch: $ret == -1\n{body}")).unwrap();
    p.validate_signature(&params(&["s", "c", "pos"]), true, true, Some("find")).unwrap();
    assert_eq!(p.exit_branch().map(|l| p.label_name(l)), Some("missing"));
    assert_err(parse_pattern(body), "undefined label");
    assert!(parse_pattern(
        "branch: $ret == -1\n$ret = call(f, $s)\nif ($ret) then a else b\na:\n    $x = 1\n    goto b\nb:\n    $y = 2"
    )
    .is_err());
    assert!(parse_pattern(&format!("branch: $r == 0\n{body}"))
        .unwrap()
        .validate_signature(&params(&["s", "c", "pos"]), false, false, Some("find"))
        .is_err());
    assert!(parse_pattern(&format!("branch: $q == 0\n{body}"))
        .unwrap()
        .validate_signature(&params(&["s", "c", "pos"]), true, false, Some("find"))
        .is_err());
}

#[test]
fn const_data_argument() {
    let body = "set_var_field.b($s, 0x17, 4)\nset_var_field.d($s, 0, $chars)\nset_var_field.b($s, 4, 0)\n";
    let mut p = parse_pattern(&format!("result: call(ctor, &$s, const_data($chars, 4), 4)\n{body}")).unwrap();
    p.validate_signature(&params(&["s", "str", "n"]), false, false, Some("ctor")).unwrap();
    let args: Vec<&str> = p.argument_placeholders().iter().map(|id| p.ph_name(*id)).collect();
    assert_eq!(args, vec!["s", "chars"]);
    assert!(parse_pattern(&format!("result: call(ctor, &$s, const_data($chars), 4)\n{body}"))
        .unwrap()
        .validate_signature(&params(&["s", "str", "n"]), false, false, Some("ctor"))
        .is_err());
    assert!(parse_pattern(&format!("result: call(ctor, &$s, const_data($chars, 9), 4)\n{body}"))
        .unwrap()
        .validate_signature(&params(&["s", "str", "n"]), false, false, Some("ctor"))
        .is_err());
    parse_pattern(&format!("result: call(ctor, &$s, const_data($chars, 8), 4)\n{body}"))
        .unwrap()
        .validate_signature(&params(&["s", "str", "n"]), false, false, Some("ctor"))
        .unwrap();
    let image = "set_var_field.b($s, 0x17, $n)\nset_var_field($s, 0, const_data($chars, $n))\n";
    let mut p = parse_pattern(&format!("result: call(ctor, &$s, const_data($chars, $n), $n)\n{image}")).unwrap();
    p.validate_signature(&params(&["s", "str", "n"]), false, false, Some("ctor")).unwrap();
    let args: Vec<&str> = p.argument_placeholders().iter().map(|id| p.ph_name(*id)).collect();
    assert_eq!(args, vec!["s", "chars", "n"]);
    assert!(parse_pattern(&format!("result: call(ctor, &$s, const_data($chars, $m), $n)\n{image}"))
        .unwrap()
        .validate_signature(&params(&["s", "str", "n"]), false, false, Some("ctor"))
        .is_err());
    assert_err(parse_pattern("set_var_field.d($s, 0, const_data($chars, $n))\n"), "no size");
    assert_err(parse_pattern("$x = const_data($chars, 3)\n"), "only be the value");
    assert_err(parse_pattern("call(f, const_data($chars, 3))\n"), "only be the value");
    assert_err(parse_pattern("set_var_field($s, $a + 1, const_data($chars, $n))\n"), "placeholder or constant offset");
}

#[test]
fn noret_and_return_end_blocks() {
    let p = parse_pattern(
        "
if ($n == -1) then oops else ok
oops:
    call(_)
    noret()
ok:
    $ret = $n
    goto done
done:
",
    )
    .unwrap();
    assert_eq!(p.blocks.len(), 4);
    assert!(matches!(p.blocks[1].terminator(), Some(Stmt::Expr(Expr::Op(o))) if o.op == Op::Noret));
    let p = parse_pattern(
        "
if ($n == -1) then early else ok
early:
    return 0
ok:
    $ret = $n
    goto done
done:
",
    )
    .unwrap();
    assert!(matches!(p.blocks[1].terminator(), Some(Stmt::Ret(_))));
    assert!(parse_pattern("$x = $n\nnoret()").is_err());
    assert!(parse_pattern("if ($n == -1) then a else b\na:\n    $x = 1\nb:\n    $ret = $n").is_err());
}

const RULES: &str = "
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

#[test]
fn parse_rules_chunk() {
    let p = parse_pattern(RULES).unwrap();
    assert!(p.is_rules());
    assert_eq!(p.rules_name.as_deref(), Some("libc++ string idioms"));
    assert_eq!(p.rules.len(), 9);
    assert_eq!(p.rules[0].lhs.as_op().unwrap().op, Op::CmpNe);
    assert_eq!(p.rules[0].rhs.as_op().unwrap().op, Op::CmpSlt);
    assert!(p.rules[0].when.is_none());
    assert_eq!(p.rules[6].when.as_ref().unwrap().as_op().unwrap().op, Op::CmpSge);
    assert_err(parse_pattern("rewrite: sx($b) => zx($c)"), "does not occur on the left");
    assert_err(parse_pattern("signature: int f(int a)\nrewrite: sx($b) => zx($b)\n$ret = $a"), "chunk of their own");
    assert_err(parse_pattern("rewrite: $b => zx($b)"), "left side of a rewrite rule");
    assert_err(parse_pattern("rules: nothing here"), "at least one");
}

#[test]
fn negation() {
    let p = parse_pattern("$r = $a s< 0").unwrap();
    let Stmt::SetVar { src, .. } = &p.blocks[0].stmts[0] else { panic!() };
    let n = negate(src).unwrap();
    assert_eq!(n.as_op().unwrap().op, Op::CmpSge);
    assert_eq!(negate(&n).unwrap().as_op().unwrap().op, Op::CmpSlt);
    let p = parse_pattern("$r = $a + 1").unwrap();
    let Stmt::SetVar { src, .. } = &p.blocks[0].stmts[0] else { panic!() };
    assert!(negate(src).is_none());
}

#[test]
fn value_pattern() {
    let p = parse_pattern("signature: bool empty(struct S* s) __pure\nvalue: call(size, $s) == 0\n").unwrap();
    let v = p.value.as_ref().unwrap().as_op().unwrap();
    assert_eq!(v.op, Op::CmpE);
    let call = v.args[0].as_call().unwrap();
    assert!(matches!(&call.target, Expr::Symbol(s) if s.name == "size"));
    assert_eq!(call.args, vec![Expr::Placeholder(p.ph("s").unwrap())]);
    let mut q = p.clone();
    q.validate_signature(&params(&["s"]), true, true, None).unwrap();
    assert_err(p.clone().validate_signature(&params(&["s"]), false, false, None), "returns a value");
    assert_err(parse_pattern("value: [$s].b\n$ret = 1"), "cannot also contain");
    assert_err(parse_pattern("value: $s"), "bare name");
    assert_err(parse_pattern("value: [$ret].b").unwrap().validate_signature(&[], true, false, None), "no meaning");
}

#[test]
fn intrinsic_statements() {
    let p = parse_pattern(
        "
            $lo, $hi = intrinsic(\"_umul128\", $a, $b)
            intrinsic(\"__dmb\", 0xb)
            $r, ... = intrinsic(\"*sqrt*\", $x, ...)
            ... = intrinsic(\"__nop\")
            _, $y = intrinsic(\"pair\", $a)
        ",
    )
    .unwrap();
    let s = &p.blocks[0].stmts;
    let Stmt::Intrinsic(c) = &s[0] else { panic!() };
    assert_eq!(c.outputs, vec![Dest::Ph(p.ph("lo").unwrap()), Dest::Ph(p.ph("hi").unwrap())]);
    assert_eq!(c.name.name, "_umul128");
    assert_eq!(c.args, vec![Expr::Placeholder(p.ph("a").unwrap()), Expr::Placeholder(p.ph("b").unwrap())]);
    assert!(!c.variadic && !c.extra_outputs);
    let Stmt::Intrinsic(c) = &s[1] else { panic!() };
    assert!(c.outputs.is_empty());
    assert_eq!(c.args, vec![Expr::Const(0xb)]);
    let Stmt::Intrinsic(c) = &s[2] else { panic!() };
    assert!(c.name.is_glob() && c.variadic && c.extra_outputs);
    assert_eq!(c.outputs.len(), 1);
    let Stmt::Intrinsic(c) = &s[3] else { panic!() };
    assert!(c.outputs.is_empty() && c.extra_outputs && c.args.is_empty());
    let Stmt::Intrinsic(c) = &s[4] else { panic!() };
    assert_eq!(c.outputs, vec![Dest::Wildcard, Dest::Ph(p.ph("y").unwrap())]);
    // The outputs count as assigned, the arguments as used.
    assert!(p.assigned_placeholders().contains(p.ph("hi").unwrap()));
    assert!(p.placeholders().contains(p.ph("x").unwrap()));
    // An intrinsic names its operation with a string and is a statement, not a value.
    assert_err(parse_pattern("$x = intrinsic(_umul128, $a)\n"), "quoted string");
    assert_err(parse_pattern("$x = intrinsic(\"f\", $a) + 1\n"), "");
}

#[test]
fn a_leading_label_names_the_first_block() {
    let p = parse_pattern("loop:\n$a = intrinsic(\"__ldaxr\", $o)\nif ($a != 0) then loop else done\ndone:\n").unwrap();
    assert_eq!(p.blocks.len(), 2);
    assert_eq!(p.blocks[0].label, p.label("loop"));
    assert_eq!(p.blocks[0].stmts.len(), 2);
}
