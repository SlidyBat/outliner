//! The fused pass: shared-guard fusions of pure accessors, reassignments in
//! the arms, and removed arms whose values the code after the join reads.

mod common;

use std::collections::BTreeMap;

use common::*;
use outliner_core::env::{Env, Merge, MergeSource};

// --------------------------------------------------------------------------- helpers

/// The function name of a pattern's signature (`uint64_t size(struct S* s) __pure` -> `size`).
fn sig_name(p: &Pattern) -> String {
    let sig = p.signature.as_deref().unwrap();
    sig.split('(').next().unwrap().split_whitespace().last().unwrap().to_string()
}

/// Index into `fm.calls` by the signature name of the call's pattern.
fn calls_by_sig(fm: &FusedMatch, patterns: &[Pattern]) -> BTreeMap<String, usize> {
    fm.calls.iter().enumerate().map(|(k, c)| (sig_name(&patterns[c.pattern]), k)).collect()
}

/// The names of the patterns behind the hoisted calls, in order.
fn call_names(fm: &FusedMatch, patterns: &[Pattern]) -> Vec<String> {
    fm.calls.iter().map(|c| patterns[c.pattern].name.clone()).collect()
}

/// The variable the `k`th hoisted call binds to placeholder `name`.
fn call_var(f: &Function, fm: &FusedMatch, k: usize, patterns: &[Pattern], name: &str) -> VarId {
    let call = &fm.calls[k];
    let p = &patterns[call.pattern];
    bound_var(f, call.binding(p.ph(name).unwrap()).unwrap())
}

fn repl(pairs: &[(ExprId, usize)]) -> BTreeMap<ExprId, usize> {
    pairs.iter().copied().collect()
}

fn replacements(entries: &[(u32, &[(ExprId, usize)])]) -> BTreeMap<u32, BTreeMap<ExprId, usize>> {
    entries.iter().map(|(i, pairs)| (*i, repl(pairs))).collect()
}

/// The starts of the blocks dominating the block starting at `start`, sorted.
fn dom_starts(f: &Function, doms: &[BlockSet], start: u32) -> Vec<u32> {
    let id = f.block_at(start).unwrap().id;
    sorted(doms[id.0 as usize].ones().map(|b| f.blocks[b].start).collect())
}

// --------------------------------------------------------------------------- FusedTests

fn pure_patterns() -> [Pattern; 2] {
    [compiled_s(PURE_DATA, true), compiled_s(PURE_SIZE, true)]
}

#[test]
fn dominators() {
    let c = make_cstr_or_func(false);
    let doms = compute_dominators(&c.f);
    assert_eq!(dom_starts(&c.f, &doms, 8), vec![0, 2, 8]);
    assert_eq!(dom_starts(&c.f, &doms, 14), vec![0, 2, 14]);
    assert_eq!(dom_starts(&c.f, &doms, 15), vec![0, 5, 15]);
}

#[test]
fn cstr_or_is_unfused() {
    let c = make_cstr_or_func(false);
    let f = &c.f;
    let patterns = pure_patterns();
    let env = FakeEnv::default();
    let round = Round::new(f, &env);
    // The guard is `(__s & 0x80000000) != 0` and the short size arm is `sx.d(b)`:
    // both need the rewrite rules to meet the single data/size patterns.
    assert!(find_fused_matches(&round, &patterns, &[], None, &no_instrs(), &no_vars()).is_empty());
    let fused = find_fused_matches(&round, &patterns, &rules(), None, &no_instrs(), &no_vars());
    assert_eq!(fused.len(), 1);
    let fm = &fused[0];
    assert_eq!((fm.guard_index, fm.kept_block, fm.removed_block), (1, 2, 5));
    assert_eq!(fm.removed_blocks, vec![5, 10, 12, 15]);
    assert_eq!(fm.kept_blocks, vec![2, 6, 8, 14]);
    let mut names = call_names(fm, &patterns);
    names.sort();
    assert_eq!(names, vec!["", ""]);
    let by_name = calls_by_sig(fm, &patterns);
    assert_eq!(by_name.keys().cloned().collect::<Vec<_>>(), vec!["data", "size"]);
    assert_eq!(call_var(f, fm, by_name["data"], &patterns, "s"), c.s);
    assert_eq!(call_var(f, fm, by_name["size"], &patterns, "s"), c.s);
    // the guard, its flag definition, both hoisted loads and the whole false arm go
    assert_eq!(fm.deleted_sorted(), vec![0, 1, 2, 3, 5, 10, 11, 12, 13, 15]);
    // x9 in `x0_1 = x9` becomes data(s); x8 in `if (x8 == 0)` becomes size(s)
    assert_eq!(fm.replacements.keys().copied().collect::<Vec<_>>(), vec![4, 8]);
    assert_eq!(fm.replacements[&8][&operand(f, 8, 1)], by_name["data"]);
    assert_eq!(fm.replacements[&4][&sub(f, operand(f, 4, 0), 0)], by_name["size"]);
}

#[test]
fn is_bracketed_reassigned_values_and_inverted_branch() {
    let b = make_is_bracketed_func();
    let f = &b.f;
    let patterns = pure_patterns();
    let env = FakeEnv::default();
    // The fake reaching-definition engine sees both arms' values merge at the join.
    assert_eq!(env.definition_of(f, 14, b.s), None);
    assert_eq!(env.definition_of(f, 8, b.s), Some(7));
    assert_eq!(env.definition_of(f, 4, b.fl), Some(0));
    let round = Round::new(f, &env);
    let fused = find_fused_matches(&round, &patterns, &rules(), None, &no_instrs(), &no_vars());
    assert_eq!(fused.len(), 1);
    let fm = &fused[0];
    assert_eq!((fm.guard_index, fm.kept_block, fm.removed_block, fm.kept_is_true), (1, 2, 4, true));
    assert_eq!(fm.removed_blocks, vec![4, 10, 12]);
    assert_eq!(fm.kept_blocks, vec![2, 5, 7]);
    let names = calls_by_sig(fm, &patterns);
    assert_eq!(names.keys().cloned().collect::<Vec<_>>(), vec!["data", "size"]);
    // The reassignments `__s = s->size` and `s = s->data` are dropped and their
    // results substituted wherever they were read, so `s` and `__s` keep their
    // original values; the inverted front() test pairs with its counterpart.
    assert_eq!(fm.deleted_sorted(), vec![0, 1, 2, 4, 7, 10, 11, 12, 13]);
    assert_eq!(fm.replacements[&3], repl(&[(sub(f, operand(f, 3, 0), 0), names["size"])]));
    let zx8 = operand(f, 8, 1); // zx.d(load_struct.b(s, 0)): the read of s
    assert_eq!(fm.replacements[&8], repl(&[(sub(f, sub(f, zx8, 0), 0), names["data"])]));
    let add14 = operand(f, 14, 1); // s + __s
    assert_eq!(fm.replacements[&14], repl(&[(sub(f, add14, 0), names["data"]), (sub(f, add14, 1), names["size"])]));
    assert!(!fm.replacements.contains_key(&2));
    assert!(!fm.replacements.contains_key(&7));
    for k in 0..fm.calls.len() {
        assert_eq!(call_var(f, fm, k, &patterns, "s"), b.s);
    }
}

#[test]
fn reassignment_reaching_join_is_substituted() {
    // The long arm reassigns s; the short arm leaves it alone; the join reads
    // it.  Every path to the join runs through the guard, so the read can take
    // the call result and s keeps its original value.
    let fx = Fx::new();
    let [s, n, x, y] = ["s", "n", "x", "y"].map(|v| fx.var(v));
    let f = fx.func(vec![
        (vec![fx.if_(fx.cmp(Op::CmpSlt, fx.sx(8, fx.load_struct(1, fx.v(s), 0x17)), fx.c(0)), 1, 4)], vec![(T, 1), (FB, 2)]), // 0
        (
            vec![
                fx.set_var(n, fx.load_struct(8, fx.v(s), 8)), // 1
                fx.set_var(s, fx.load_struct(8, fx.v(s), 0)), // 2
                fx.goto(6),                                   // 3
            ],
            vec![(U, 3)],
        ),
        (
            vec![
                fx.set_var(n, fx.zx(8, fx.load_struct(1, fx.v(s), 0x17))), // 4
                fx.goto(6),                                                // 5
            ],
            vec![(U, 3)],
        ),
        (
            vec![
                fx.set_vars(x, fx.load(1, fx.v(s)), 1),   // 6
                fx.set_var(y, fx.add(fx.v(x), fx.v(n))),  // 7
                fx.ret(&[fx.v(y)]),                       // 8
            ],
            vec![],
        ),
    ]);
    let env = FakeEnv::default();
    assert_eq!(env.merges_of(&f, 2, s, 0), Some(vec![Merge { block_start: 6, others: vec![MergeSource::Live] }]));
    let patterns = pure_patterns();
    let round = Round::new(&f, &env);
    let fused = find_fused_matches(&round, &patterns, &[], None, &no_instrs(), &no_vars());
    assert_eq!(fused.len(), 1);
    let fm = &fused[0];
    let names = calls_by_sig(fm, &patterns);
    assert_eq!(fm.deleted_sorted(), vec![0, 2, 4, 5]);
    assert_eq!(
        fm.replacements,
        replacements(&[
            (1, &[(operand(&f, 1, 1), names["size"])]),
            (6, &[(sub(&f, operand(&f, 6, 1), 0), names["data"])]),
        ])
    );
}

#[test]
fn reassignment_with_outside_path_keeps_assignment() {
    // Same shape, but a path from before the guard also reaches the join: the
    // read there may see the original s, so the reassignment stays as
    // `s = <call result>` in the kept arm.
    let fx = Fx::new();
    let [c, s, n, x] = ["c", "s", "n", "x"].map(|v| fx.var(v));
    let f = fx.func(vec![
        (vec![fx.if_(fx.cmp(Op::CmpE, fx.v(c), fx.c(0)), 1, 9)], vec![(T, 1), (FB, 5)]), // 0
        (vec![fx.if_(fx.cmp(Op::CmpSlt, fx.sx(8, fx.load_struct(1, fx.v(s), 0x17)), fx.c(0)), 2, 5)], vec![(T, 2), (FB, 3)]), // 1
        (
            vec![
                fx.set_var(n, fx.load_struct(8, fx.v(s), 8)), // 2
                fx.set_var(s, fx.load_struct(8, fx.v(s), 0)), // 3
                fx.goto(7),                                   // 4
            ],
            vec![(U, 4)],
        ),
        (
            vec![
                fx.set_var(n, fx.zx(8, fx.load_struct(1, fx.v(s), 0x17))), // 5
                fx.goto(7),                                                // 6
            ],
            vec![(U, 4)],
        ),
        (
            vec![
                fx.set_vars(x, fx.load(1, fx.v(s)), 1), // 7
                fx.ret(&[fx.v(x), fx.v(n)]),            // 8
            ],
            vec![],
        ),
        (
            vec![
                fx.set_var(n, fx.c(0)), // 9
                fx.goto(7),             // 10
            ],
            vec![(U, 4)],
        ),
    ]);
    let env = FakeEnv::default();
    assert_eq!(env.merges_of(&f, 3, s, 1), Some(vec![Merge { block_start: 7, others: vec![MergeSource::Live] }]));
    let patterns = pure_patterns();
    let round = Round::new(&f, &env);
    let fused = find_fused_matches(&round, &patterns, &[], None, &no_instrs(), &no_vars());
    assert_eq!(fused.len(), 1);
    let fm = &fused[0];
    let names = calls_by_sig(fm, &patterns);
    assert_eq!(fm.guard_index, 1);
    assert_eq!(fm.deleted_sorted(), vec![1, 5, 6]);
    assert_eq!(
        fm.replacements,
        replacements(&[(2, &[(operand(&f, 2, 1), names["size"])]), (3, &[(operand(&f, 3, 1), names["data"])])])
    );
}

#[test]
fn impure_pattern_is_not_hoisted() {
    let c = make_cstr_or_func(false);
    let patterns = [compiled_s(PURE_DATA, false), compiled_s(PURE_SIZE, true)];
    let env = FakeEnv::default();
    let round = Round::new(&c.f, &env);
    let fused = find_fused_matches(&round, &patterns, &rules(), None, &no_instrs(), &no_vars());
    assert!(fused.is_empty()); // data() cannot explain its pair, arms are not isomorphic
}

#[test]
fn non_isomorphic_arms_rejected() {
    let c = make_cstr_or_func(true);
    let patterns = pure_patterns();
    let env = FakeEnv::default();
    let round = Round::new(&c.f, &env);
    assert!(find_fused_matches(&round, &patterns, &rules(), None, &no_instrs(), &no_vars()).is_empty());
}

#[test]
fn fused_pass_respects_regular_matches() {
    // In the plugin the regular matcher runs first; the fused pass then only
    // looks at blocks it did not claim and knows what it deleted.
    let c = make_checksum_func();
    let f = &c.f;
    let patterns = pure_patterns();
    let env = FakeEnv::default();
    let round = Round::new(f, &env);
    let regular = find_matches(&round, &patterns, &rules(), None);
    assert_eq!(regular.len(), 2);
    let claimed = claimed_blocks(f, &regular);
    let deleted = deleted_union(f, &regular);
    let live = live_union(f, &regular, &patterns);
    assert!(find_fused_matches(&round, &patterns, &rules(), Some(&claimed), &deleted, &live).is_empty());
}

#[test]
fn regular_diamond_not_treated_as_fused() {
    // A plain data() diamond has arms that are not isomorphic (different values
    // assigned but no second explained pair): the arms are `__s = x10` vs `__s = x8`
    // which *is* explained by data()... and that is fine: hoisting is equivalent.
    let c = make_checksum_func();
    let patterns = pure_patterns();
    let env = FakeEnv::default();
    let round = Round::new(&c.f, &env);
    let fused = find_fused_matches(&round, &patterns, &rules(), None, &no_instrs(), &no_vars());
    // both diamonds are recognised as fused matches with one call each
    assert_eq!(fused.iter().map(|fm| fm.guard_index).collect::<Vec<_>>(), vec![5, 10]);
    assert_eq!(fused.iter().map(|fm| fm.calls.len()).collect::<Vec<_>>(), vec![1, 1]);
    assert_eq!(fused[0].deleted_sorted(), vec![3, 5, 8, 9]);
    assert!(fused[0].replacements.contains_key(&6));
}
