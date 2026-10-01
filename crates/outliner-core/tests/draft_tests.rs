//! Drafting patterns from code: a selected region or a whole function comes
//! back as text that parses and matches the code it came from.

mod common;

use common::*;
use outliner_core::draft::{draft_function, draft_region};

const RELEASE_COUNT: &str = "
    goto loop
loop:
    $result = intrinsic(\"__ldaxr\", $o)
    $x19_1 = $result
    $x8_1 = $x19_1 - 1
    $cond_0_1 = $x19_1 != 1
    $i = intrinsic(\"__stlxr\", $x8_1, $o)
    $x9_1 = $i
    if ($x9_1 != 0) then loop else after
after:
    if ($cond_0_1) then ret else freed
ret:
    $x0 = $x19_1
    return $x0
freed:
    call(\"_free\", $o)
    goto ret
";

fn env(l: &Loaded) -> FakeEnv {
    l.env(&[], vec![], Structs::new(), &[])
}

#[test]
fn a_loop_region_drafts_a_pattern_that_matches_itself() {
    let l = from_pattern_text(RELEASE_COUNT, &[("o", "struct Object*")]).unwrap();
    let f = &l.func;
    let env = env(&l);
    let draft = draft_region(f, &env, None, &(1..=7).collect::<Vec<u32>>(), "refcnt_dec").unwrap();
    let text = &draft.text;
    assert!(text.starts_with("signature: int64_t refcnt_dec(struct Object* o)\n$o : struct Object*\n"), "{text}");
    assert!(text.contains("entry:\n"), "{text}");
    assert!(text.contains("$ret = $result"), "{text}");
    assert!(text.contains("then entry else done"), "{text}");
    assert!(text.trim_end().ends_with("done:"), "{text}");
    assert_eq!(draft.params, vec![("o".to_string(), Some("struct Object*".to_string()))]);
    assert_eq!(draft.ret.as_ref().map(|r| r.0.as_str()), Some("x19_1"));
    // The condition computed in the loop is read afterwards too: it becomes a
    // declared output, computed from the call's value.
    assert!(text.contains("result: $cond_0_1 = (call(refcnt_dec, $o) != 0x1)"), "{text}");
    let p = compiled(text, &["o"], true, false);
    let round = Round::new(f, &env);
    let matches = find_matches(&round, &[p], &[], None);
    assert_eq!(matches.len(), 1);
    assert_eq!(matches[0].ret_var(f), Some(l.var("x19_1")));
}

#[test]
fn a_leading_jump_into_the_selection_is_left_out() {
    // Selecting the jump into the loop as well gives the same pattern: one that
    // started with the jump would only match code that has it.
    let l = from_pattern_text(RELEASE_COUNT, &[("o", "struct Object*")]).unwrap();
    let f = &l.func;
    let env = env(&l);
    let from_loop = draft_region(f, &env, None, &(1..=7).collect::<Vec<u32>>(), "refcnt_dec").unwrap();
    let with_jump = draft_region(f, &env, None, &(0..=7).collect::<Vec<u32>>(), "refcnt_dec").unwrap();
    assert_eq!(with_jump.text, from_loop.text);
    assert!(with_jump.notes.iter().any(|n| n.contains("jump")), "{:?}", with_jump.notes);
    assert!(!from_loop.notes.iter().any(|n| n.contains("jump")), "{:?}", from_loop.notes);
}

#[test]
fn a_diamond_region_gets_labels_and_an_exit() {
    let (f, s, r) = make_c_str_func(Some("struct std::string*"), false);
    let env = FakeEnv::default();
    let region: Vec<u32> = (0..f.len() as u32).filter(|i| f.instr_op(*i) != outliner_core::ops::Op::Ret).collect();
    let draft = draft_region(&f, &env, None, &region, "c_str").unwrap();
    let text = &draft.text;
    assert!(text.contains("signature: char const* c_str(struct std::string* s)"), "{text}");
    assert!(text.contains("L1:") && text.contains("L2:") && text.contains("done:"), "{text}");
    assert!(text.contains("goto done"), "{text}");
    assert_eq!(draft.ret.as_ref().map(|r| r.0.as_str()), Some(f.var_name(r)));
    assert_eq!(draft.params[0].0, f.var_name(s));
    let p = compiled(text, &["s"], true, false);
    let round = Round::new(&f, &env);
    assert_eq!(find_matches(&round, &[p], &[], None).len(), 1);
}

#[test]
fn a_selection_that_leaves_twice_is_refused() {
    let l = from_pattern_text(RELEASE_COUNT, &[("o", "struct Object*")]).unwrap();
    let env = env(&l);
    // The loop plus the join's branch: two blocks are left through.
    let err = draft_region(&l.func, &env, None, &(1..=8).collect::<Vec<u32>>(), "f").unwrap_err();
    assert!(err.contains("several blocks"), "{err}");
    // A block entered from outside the selection.
    let err = draft_region(&l.func, &env, None, &[9, 10, 11, 12], "f").unwrap_err();
    assert!(err.contains("entered from"), "{err}");
}

#[test]
fn a_function_drafts_with_its_parameters_and_returns() {
    let l = from_pattern_text(
        "
    $__s = sx.q(load_struct.b($s, 0x17))
    if (($__s s< 0)) then long else short
long:
    $r = [$s].q
    return $r
short:
    return $s
",
        &[("s", "struct std::string*")],
    )
    .unwrap();
    let env = env(&l);
    let draft = draft_function(&l.func, &env, None, &[l.var("s")], "char const* c_str(struct std::string* s)", true).unwrap();
    let text = &draft.text;
    assert!(text.starts_with("signature: char const* c_str(struct std::string* s)\n$s : struct std::string*\n"), "{text}");
    assert!(text.contains("$ret = $r") && text.contains("$ret = $s"), "{text}");
    assert!(text.contains("goto done") && text.trim_end().ends_with("done:"), "{text}");
    let p = compiled(text, &["s"], true, false);
    assert_eq!(p.blocks.len(), 4);
}
