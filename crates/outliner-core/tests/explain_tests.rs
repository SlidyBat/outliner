//! Explaining failed matches and generalising from a second instance.

mod common;

use common::*;
use outliner_core::generalize::{generalize, Generalized};
use outliner_core::matcher::explain_pattern;

#[test]
fn a_type_constraint_failure_is_named() {
    let p = compiled(c_str_pattern(), &["s"], true, false);
    let (f, _, _) = make_c_str_func(Some("struct Other*"), false);
    let env = FakeEnv::default();
    let round = Round::new(&f, &env);
    let err = explain_pattern(&round, &[p.clone()], 0, &[], None).unwrap_err();
    let reason = err.attempt.reason.clone().unwrap_or_default();
    assert!(reason.contains("$s is struct Other*") && reason.contains("struct std::string*"), "{reason}");
    assert_eq!(err.attempt.matched, 0);
    let line = err.line(&p).unwrap();
    assert!(c_str_pattern().lines().nth(line as usize - 1).unwrap().contains("if ("), "{line}");
}

#[test]
fn a_wrong_operation_is_named_with_progress() {
    // The pattern's second statement expects a store where the code loads.
    let l = from_pattern_text("$a = [$p].q\n$b = [$q].q\nreturn $b\n", &[]).unwrap();
    let p = compiled("$a = [$p].q\n[$q].q = $a\n", &["p", "q"], false, false);
    let env = l.env(&[], vec![], Structs::new(), &[]);
    let round = Round::new(&l.func, &env);
    let err = explain_pattern(&round, &[p.clone()], 0, &[], None).unwrap_err();
    assert_eq!((err.start, err.attempt.matched, err.attempt.instr), (0, 1, 1));
    assert_eq!(err.line(&p), Some(2));
    assert!(err.attempt.reason.as_deref().unwrap_or("").contains("expects a store"), "{err:?}");
}

#[test]
fn a_value_still_used_after_the_region_is_named() {
    let l = from_pattern_text("$a = [$p].q\n$b = $a + 1\n$c = $b + 2\nreturn $c\n", &[]).unwrap();
    // The pattern consumes $b but the code reads it afterwards.
    let p = compiled("$a = [$p].q\n$ret = $a + 1\n$x = $ret + 2\n", &["p"], true, false);
    let env = l.env(&[], vec![], Structs::new(), &[]);
    let round = Round::new(&l.func, &env);
    let err = explain_pattern(&round, &[p], 0, &[], None).unwrap_err();
    assert!(err.attempt.reason.as_deref().unwrap_or("").contains("still read after"), "{err:?}");
}

#[test]
fn an_instruction_left_between_matched_statements_is_quoted() {
    // The comparison sits between the two matched statements and reads the
    // loaded value, which the call will compute: the reason quotes it and says
    // how the pattern can take it in.
    let l = from_pattern_text("$a = [$p].q\n$c = $a != 1\n$b = $a + 1\nreturn $b, $c\n", &[]).unwrap();
    let p = compiled("$old = [$p].q\n$ret = $old + 1\n", &["p"], true, false);
    let env = l.env(&[], vec![], Structs::new(), &[]);
    let round = Round::new(&l.func, &env);
    let err = explain_pattern(&round, &[p], 0, &[], None).unwrap_err();
    let reason = err.attempt.reason.unwrap_or_default();
    assert!(reason.contains("instruction 1 (`$c = ($a != 0x1)`)"), "{reason}");
    assert!(reason.contains("reads a, which the region computes"), "{reason}");
    assert!(reason.contains("add the instruction to the pattern, with a 'result:' line for $c"), "{reason}");
}

#[test]
fn a_match_is_returned_when_there_is_one() {
    let p = compiled(c_str_pattern(), &["s"], true, false);
    let (f, _, _) = make_c_str_func(Some("struct std::string*"), false);
    let env = FakeEnv::default();
    let round = Round::new(&f, &env);
    assert!(explain_pattern(&round, &[p], 0, &[], None).is_ok());
}

#[test]
fn differing_constants_become_placeholders() {
    let first = parse_pattern("signature: int f(int* p)\n$ret = [$p].d\n$x = $ret + 8\n[$p].d = $x\n").unwrap();
    let second = parse_pattern("$ret = [$q].d\n$y = $ret + 0x10\n[$q].d = $y\n").unwrap();
    let Generalized::Merged { text, notes } = generalize(&first, &second) else { panic!("merged") };
    assert!(text.contains("signature: int f(int* p)"), "{text}");
    assert!(text.contains("$x = ($ret + $k1)"), "{text}");
    assert!(text.contains("[$p].d = $x"), "{text}");
    assert!(notes.iter().any(|n| n.contains("$k1") && n.contains("0x8") && n.contains("0x10")), "{notes:?}");
    // The merged text is a pattern again.
    parse_pattern(&text).unwrap();
}

#[test]
fn a_different_shape_becomes_a_chunk() {
    let first = parse_pattern("signature: int f(int* p)\n$ret = [$p].d\n").unwrap();
    let second = parse_pattern("$ret = [$q].d\n$z = $ret + 1\n").unwrap();
    let Generalized::Chunk { text, why } = generalize(&first, &second) else { panic!("chunk") };
    assert!(why.contains("statements"), "{why}");
    assert!(text.starts_with("signature: int f(int* p)\n"), "{text}");
    assert!(text.contains("$z = ($ret + 0x1)"), "{text}");
}

#[test]
fn placeholders_that_stand_for_two_things_are_a_chunk() {
    let first = parse_pattern("$a = [$p].d\n$b = [$p].d\n").unwrap();
    let second = parse_pattern("$a = [$p].d\n$b = [$q].d\n").unwrap();
    assert!(matches!(generalize(&first, &second), Generalized::Chunk { .. }));
}

#[test]
fn a_result_line_only_the_second_instance_has_is_kept() {
    // The second instance's code reads the decremented count afterwards, so its
    // draft declares it; the merge must keep that line, in the first pattern's
    // names and for its function.
    let first = parse_pattern("signature: int f(int* p)\n$ret = [$p].d\n$x = $ret - 1\n[$p].d = $x\n").unwrap();
    let second =
        parse_pattern("signature: int outlined(int* q)\nresult: $y = call(outlined, $q) - 1\n$ret = [$q].d\n$y = $ret - 1\n[$q].d = $y\n").unwrap();
    let Generalized::Merged { text, notes } = generalize(&first, &second) else { panic!("merged") };
    assert!(text.contains("result: $x = (call(f, $p) - 0x1)"), "{text}");
    assert!(notes.iter().any(|n| n.contains("result") && n.contains("$x")), "{notes:?}");
    parse_pattern(&text).unwrap();
}

#[test]
fn result_lines_are_generalised_with_the_body() {
    let first = parse_pattern("signature: int f(int* p)\nresult: $x = call(f, $p) - 1\n$ret = [$p].d\n$x = $ret - 1\n[$p].d = $x\n").unwrap();
    let second =
        parse_pattern("signature: int outlined(int* q)\nresult: $y = call(outlined, $q) - 2\n$ret = [$q].d\n$y = $ret - 2\n[$q].d = $y\n").unwrap();
    let Generalized::Merged { text, .. } = generalize(&first, &second) else { panic!("merged") };
    assert!(text.contains("$x = ($ret - $k1)"), "{text}");
    assert!(text.contains("result: $x = (call(f, $p) - $k1)"), "{text}");
}

#[test]
fn conflicting_declarations_stay_separate_chunks() {
    // What $ret holds differs: the second instance returns the decremented count.
    let first = parse_pattern("signature: int f(int* p)\n$ret = [$p].d\n$x = $ret - 1\n[$p].d = $x\n").unwrap();
    let second =
        parse_pattern("signature: int outlined(int* q)\nresult: call(outlined, $q) - 1\n$ret = [$q].d\n$y = $ret - 1\n[$q].d = $y\n").unwrap();
    let Generalized::Chunk { text, why } = generalize(&first, &second) else { panic!("chunk") };
    assert!(why.contains("$ret"), "{why}");
    // the chunk speaks of the first pattern's function, so it validates under its signature
    assert!(text.starts_with("signature: int f(int* p)\nresult: (call(f, $q) - 0x1)\n"), "{text}");
    parse_pattern(&text).unwrap();
    // A value: pattern does not merge into a statement pattern.
    let value = parse_pattern("signature: int outlined(int* q)\nvalue: [$q].d\n").unwrap();
    let Generalized::Chunk { why, .. } = generalize(&first, &value) else { panic!("chunk") };
    assert!(why.contains("value:") || why.contains("statements") || why.contains("blocks"), "{why}");
}

#[test]
fn an_edited_pattern_keeps_its_result_lines() {
    // The first pattern was edited to say what $ret holds; the second is a raw
    // draft of another instance, which never writes such a line.
    let first =
        parse_pattern("signature: int f(int* p)\nresult: call(f, $p) - 1\n$old = [$p].d\n$ret = $old - 1\n[$p].d = $ret\n").unwrap();
    let second = parse_pattern("signature: int outlined(int* q)\n$o = [$q].d\n$ret = $o - 1\n[$q].d = $ret\n").unwrap();
    let Generalized::Merged { text, .. } = generalize(&first, &second) else { panic!("merged") };
    assert!(text.contains("result: (call(f, $p) - 0x1)"), "{text}");
    parse_pattern(&text).unwrap();
}

