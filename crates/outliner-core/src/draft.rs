//! Drafting a pattern from code: a region of a function's MLIL (what the
//! user selected) or a whole function, with its parameters, result and shape
//! worked out, so that writing a pattern starts from a text that already
//! describes the code.

use std::collections::{BTreeMap, BTreeSet};

use crate::env::Env;
use crate::il::{Function, InstrSet, VarId};
use crate::ops::Op;
use crate::render::{placeholder, render_lines, render_stmt, SymbolLookup};

/// A drafted pattern and what was decided about it.
#[derive(Clone, Debug, Default)]
pub struct Draft {
    /// The pattern text: signature, constraints and body.
    pub text: String,
    /// Parameters: placeholder name and type spelling (None when untyped).
    pub params: Vec<(String, Option<String>)>,
    /// The result variable's placeholder name and type, when there is one.
    pub ret: Option<(String, Option<String>)>,
    /// Things the user should look at.
    pub notes: Vec<String>,
}

/// The region's control flow as the pattern needs it.
struct Shape {
    entry_block: u32,
    /// The block every exit leads to, when the region leaves through labelled blocks.
    exit: Option<u32>,
    /// Block starts of the blocks other than the entry, in index order.
    internal: Vec<u32>,
    /// A branch inside the selection leads back to the entry block (a loop).
    loops_to_entry: bool,
}

fn shape(f: &Function, region: &InstrSet) -> Result<Shape, String> {
    let first = region.ones().next().ok_or("the selection is empty")? as u32;
    let entry = f.block_of(first);
    let mut internal: Vec<u32> = Vec::new();
    for block in &f.blocks {
        let selected: Vec<u32> = block.range().filter(|i| region.contains(*i as usize)).collect();
        if selected.is_empty() {
            continue;
        }
        if block.id == entry.id {
            // The entry block is selected from its first selected instruction on, without gaps.
            let expected: Vec<u32> = (first..first + selected.len() as u32).collect();
            if selected != expected {
                return Err(format!("the selection skips instruction {} in its first block", selected.iter().zip(&expected).find(|(a, b)| a != b).map(|(_, b)| *b).unwrap_or(first)));
            }
            continue;
        }
        if selected.len() != (block.end - block.start) as usize {
            return Err(format!("the block at instruction {} is only partly selected", block.start));
        }
        internal.push(block.start);
    }
    // Every exit must lead to one block (or fall out of a straight-line selection).
    let mut exits: BTreeSet<u32> = BTreeSet::new();
    let mut falls_through = false;
    let mut loops_to_entry = false;
    for i in region.ones().map(|i| i as u32) {
        let block = f.block_of(i);
        if i + 1 < block.end {
            if !region.contains(i as usize + 1) {
                falls_through = true;
            }
            continue;
        }
        for edge in &block.outgoing {
            let target = f.block(edge.target).start;
            if target == entry.start && first == entry.start {
                loops_to_entry = true;
            } else if !region.contains(target as usize) {
                exits.insert(target);
            }
        }
    }
    if falls_through {
        if !internal.is_empty() || !exits.is_empty() || loops_to_entry {
            return Err("the selection ends inside its first block but also leaves through a branch".to_string());
        }
        return Ok(Shape { entry_block: entry.start, exit: None, internal, loops_to_entry });
    }
    if exits.len() > 1 {
        return Err(format!("the selection leaves through several blocks (instructions {:?}); a pattern has one exit", exits));
    }
    // Internal blocks are entered from the selection only.
    for start in &internal {
        let block = f.block_at(*start).ok_or("bad block")?;
        for edge in &block.incoming {
            let source = f.block(edge.source);
            let last = source.end - 1;
            if !region.contains(last as usize) {
                return Err(format!("the block at instruction {start} is entered from instruction {last}, outside the selection"));
            }
        }
    }
    Ok(Shape { entry_block: entry.start, exit: exits.into_iter().next(), internal, loops_to_entry })
}

/// Variables the region reads before writing them: `(variable, first read)`.
fn live_in(f: &Function, env: &dyn Env, region: &InstrSet) -> Vec<VarId> {
    let mut written: BTreeSet<VarId> = BTreeSet::new();
    let mut out: Vec<VarId> = Vec::new();
    for i in region.ones().map(|i| i as u32) {
        let instr = f.instr(i);
        for v in f.vars_read(instr) {
            if out.contains(&v) {
                continue;
            }
            let from_region = match env.definition_of(f, i, v) {
                Some(d) => region.contains(d as usize),
                None => written.contains(&v), // merged or opaque: written earlier in the selection, or not
            };
            if !from_region {
                out.push(v);
            }
        }
        for v in f.vars_written(instr) {
            written.insert(v);
        }
    }
    out
}

/// A variable the region writes that is read after it.
struct LiveOut {
    var: VarId,
    last_write: u32,
    /// Some use could not be located.
    unknown: bool,
    /// Read by something other than a branch test: a value, not just a condition.
    valued: bool,
}

/// Variables the region writes that are read after it, the likeliest result last.
fn live_out(f: &Function, env: &dyn Env, region: &InstrSet) -> Vec<LiveOut> {
    let mut found: BTreeMap<VarId, LiveOut> = BTreeMap::new();
    for i in region.ones().map(|i| i as u32) {
        let instr = f.instr(i);
        for v in f.vars_written(instr) {
            let uses = env.uses_of(f, i, v, None);
            let unknown = uses.contains(&u32::MAX);
            let outside: Vec<u32> = uses.iter().copied().filter(|u| *u != u32::MAX && !region.contains(*u as usize)).collect();
            let entry = found.entry(v).or_insert(LiveOut { var: v, last_write: i, unknown: false, valued: false });
            entry.last_write = i;
            if outside.is_empty() && !unknown {
                continue;
            }
            entry.unknown |= unknown;
            entry.valued |= outside.iter().any(|u| f.instr_op(*u) != Op::If);
        }
    }
    let mut out: Vec<LiveOut> = found.into_values().filter(|l| l.unknown || l.valued || region_reads_after(f, l, region)).collect();
    out.sort_by_key(|l| (l.valued, l.last_write));
    out
}

/// A condition read only by branches still counts as live when a branch outside reads it.
fn region_reads_after(f: &Function, l: &LiveOut, region: &InstrSet) -> bool {
    (0..f.len() as u32).any(|u| !region.contains(u as usize) && f.vars_read(f.instr(u)).contains(&l.var))
}

/// Prologue and epilogue bookkeeping the decompiler leaves in MLIL: saves and
/// restores of the link register and callee-saved registers.
fn is_bookkeeping(f: &Function, index: u32) -> bool {
    let instr = f.instr(index);
    if f.op(instr) != Op::SetVar {
        return false;
    }
    let noise = |v: VarId| {
        let name = f.var_name(v);
        name == "lr" || name.starts_with("lr_") || name.starts_with("__saved_") || name == "fp" || name.starts_with("fp_")
    };
    f.vars_written(instr).iter().any(|v| noise(*v)) || f.vars_read(instr).iter().any(|v| noise(*v))
}

fn rename(text: &str, from: &str, to: &str) -> String {
    // `$from` as a whole placeholder only: `$x8` must not touch `$x8_1`.
    let mut out = String::with_capacity(text.len());
    let needle = format!("${from}");
    let mut rest = text;
    while let Some(pos) = rest.find(&needle) {
        let after = &rest[pos + needle.len()..];
        let whole = !after.chars().next().is_some_and(|c| c.is_ascii_alphanumeric() || c == '_');
        out.push_str(&rest[..pos]);
        out.push_str(if whole { to } else { &needle });
        rest = after;
    }
    out.push_str(rest);
    out
}

/// Drafts a pattern for the instructions in `region` of `f`, outlining them
/// as a function called `name`.
pub fn draft_region(f: &Function, env: &dyn Env, symbols: Option<SymbolLookup>, region: &[u32], name: &str) -> Result<Draft, String> {
    let mut set = f.instr_set();
    for i in region {
        if (*i as usize) < f.len() {
            set.insert(*i as usize);
        }
    }
    for i in set.ones().map(|i| i as u32).collect::<Vec<_>>() {
        if is_bookkeeping(f, i) {
            set.set(i as usize, false);
        }
    }
    if set.count_ones(..) == 0 {
        return Err("the selection holds no instruction a pattern can describe".to_string());
    }
    // A selection that starts with a jump to its next instruction (into a loop,
    // from the block before it) starts at the target instead: a pattern that
    // begins with the jump only matches code that has one, and the labelled
    // loop matches code that reaches it either way.
    let mut dropped_jump = false;
    while let Some(first) = set.ones().next().map(|i| i as u32) {
        let instr = f.instr(first);
        let target = f.int_operand(instr, 0).map(|t| t as u32);
        let next = set.ones().nth(1).map(|i| i as u32);
        if f.op(instr) != Op::Goto || target.is_none() || next != target || f.block_of(next.unwrap()).start != next.unwrap() {
            break;
        }
        set.set(first as usize, false);
        dropped_jump = true;
    }
    let shape = shape(f, &set)?;
    let mut draft = Draft::default();
    if dropped_jump {
        draft.notes.push("the jump the selection started with was left out, so the pattern also matches code that reaches the loop without it".to_string());
    }

    let ins = live_in(f, env, &set);
    let outs = live_out(f, env, &set);
    let ret = outs.last().map(|l| l.var);
    // Other values read afterwards are declared outputs when they are plain
    // expressions over the result, else the user is told.
    let mut extra_results: Vec<String> = Vec::new();
    let mut declared: Vec<(VarId, u32)> = Vec::new();
    for l in &outs {
        let name = placeholder(f.var_name(l.var));
        if Some(l.var) != ret {
            let def = f.instr(l.last_write);
            if f.op(def) == Op::SetVar && ret.is_some_and(|r| f.vars_read(def).contains(&r)) {
                declared.push((l.var, l.last_write));
            } else {
                draft.notes.push(format!(
                    "{name} is also read after the selection: drop the lines computing it, or add `result: {name} = ...` to keep it"
                ));
            }
        } else if l.unknown {
            draft.notes.push(format!("whether {name} is read after the selection could not be told"));
        }
    }
    let spelling = |v: VarId| env.type_of_var(f, v).map(|t| env.type_spelling(t));
    for v in &ins {
        draft.params.push((placeholder(f.var_name(*v)).trim_start_matches('$').to_string(), spelling(*v)));
    }
    let ret_name = ret.map(|v| placeholder(f.var_name(v)).trim_start_matches('$').to_string());
    draft.ret = ret.map(|v| (ret_name.clone().unwrap(), spelling(v)));

    // The signature: the parameters as the code types them, the result's type.
    let ret_type = match &draft.ret {
        Some((_, Some(t))) => t.clone(),
        Some((name, None)) => {
            draft.notes.push(format!("${name} has no type in the decompiler; the signature returns int64_t until you say otherwise"));
            "int64_t".to_string()
        }
        None => "void".to_string(),
    };
    let params: Vec<String> = draft
        .params
        .iter()
        .map(|(n, t)| format!("{} {n}", t.clone().unwrap_or_else(|| "int64_t".to_string())))
        .collect();
    let mut lines: Vec<String> = vec![format!("signature: {ret_type} {name}({})", params.join(", "))];
    for (n, t) in &draft.params {
        match t {
            Some(t) => lines.push(format!("${n} : {t}")),
            None => draft.notes.push(format!("${n} has no type in the decompiler; give it a constraint if the pattern should be specific")),
        }
    }
    lines.push(String::new());

    // The body, with the region's blocks named L1.. and the exit `done`.
    let mut names: BTreeMap<u32, String> = BTreeMap::new();
    names.insert(shape.entry_block, "entry".to_string());
    for (k, start) in shape.internal.iter().enumerate() {
        names.insert(*start, format!("L{}", k + 1));
    }
    if let Some(exit) = shape.exit {
        names.insert(exit, "done".to_string());
    }
    let label = |start: u32| names.get(&start).cloned().unwrap_or_else(|| format!("L{start}"));
    let only: Vec<u32> = set.ones().map(|i| i as u32).collect();
    let mut body = render_lines(f, symbols, Some(&only), None, &label, shape.loops_to_entry);
    if let Some(r) = &ret_name {
        body = rename(&body, r, "$ret");
        // `result:` lines for the declared outputs: their defining statement's
        // right side, with the result standing for the call.
        let call = format!("call({name}, {})", draft.params.iter().map(|(n, _)| format!("${n}")).collect::<Vec<_>>().join(", "));
        for (v, at) in &declared {
            let line = rename(&render_stmt(f, *at, symbols), r, "$ret");
            if let Some((lhs, rhs)) = line.split_once(" = ") {
                let rhs = rename(rhs, "ret", &call);
                extra_results.push(format!("result: {} = {rhs}", lhs.trim()));
            }
            let _ = v;
        }
    }
    if !extra_results.is_empty() {
        let at = lines.len() - 1; // before the blank line that ends the header
        for (k, r) in extra_results.iter().enumerate() {
            lines.insert(at + k, r.clone());
        }
    }
    if body.contains("# unsupported") {
        draft.notes.push("a statement the pattern language cannot describe is left as a comment".to_string());
    }
    lines.push(body.trim_end().to_string());
    if shape.exit.is_some() {
        lines.push("done:".to_string());
    }
    draft.text = lines.join("\n") + "\n";
    if draft.ret.is_none() {
        draft.notes.push("nothing the selection computes is read afterwards: the function returns void".to_string());
    }
    Ok(draft)
}

/// Drafts a pattern from a whole function: its parameters are the pattern's,
/// every `return x` becomes `$ret = x` and the returns join in `done`.
pub fn draft_function(
    f: &Function,
    env: &dyn Env,
    symbols: Option<SymbolLookup>,
    params: &[VarId],
    signature: &str,
    returns: bool,
) -> Result<Draft, String> {
    let mut draft = Draft::default();
    let spelling = |v: VarId| env.type_of_var(f, v).map(|t| env.type_spelling(t));
    let mut lines: Vec<String> = vec![format!("signature: {signature}")];
    for v in params {
        let name = placeholder(f.var_name(*v)).trim_start_matches('$').to_string();
        let ty = spelling(*v);
        if let Some(t) = &ty {
            lines.push(format!("${name} : {t}"));
        }
        draft.params.push((name, ty));
    }
    lines.push(String::new());
    let only: Vec<u32> = (0..f.len() as u32).filter(|i| !is_bookkeeping(f, *i)).collect();
    let label = |start: u32| if start == 0 { "entry".to_string() } else { format!("L{start}") };
    let entry_targeted = f.blocks.first().is_some_and(|b| !b.incoming.is_empty());
    let body = render_lines(f, symbols, Some(&only), None, &label, entry_targeted);
    // `return x` leaves the pattern through `done` with `$ret` holding x.
    let mut out: Vec<String> = Vec::new();
    for line in body.lines() {
        let (stmt, comment) = match line.find("    #") {
            Some(pos) => (&line[..pos], &line[pos..]),
            None => (line, ""),
        };
        let trimmed = stmt.trim();
        if let Some(rest) = trimmed.strip_prefix("return") {
            let value = rest.trim();
            if returns && !value.is_empty() && !value.starts_with("call(") {
                out.push(format!("    $ret = {value}{comment}"));
            } else if !value.is_empty() && value.starts_with("call(") {
                out.push(format!("    {trimmed}{comment}"));
                continue;
            }
            out.push("    goto done".to_string());
            continue;
        }
        out.push(line.to_string());
    }
    lines.push(out.join("\n"));
    lines.push("done:".to_string());
    draft.text = lines.join("\n") + "\n";
    if returns {
        draft.ret = Some(("ret".to_string(), None));
    }
    draft.notes.push("the out-of-line body differs from the inlined shape in its prologue and merges; trim it to the statements the inlined code keeps".to_string());
    Ok(draft)
}
