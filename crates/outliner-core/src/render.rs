//! Render MLIL in the pattern language.
//!
//! The output is meant as a starting point for writing a pattern: copy the
//! lines of the inlined code, rename the placeholders that are parameters to
//! the names used in the signature, rename the result to `$ret`, drop what is
//! unrelated.  Every line carries the original instruction index and text as
//! a comment.

use crate::il::{ExprId, Function, Operand};
use crate::ops::{size_suffix, Op};

/// Names an address has, for printing call targets.
pub type SymbolLookup<'a> = &'a dyn Fn(u64) -> Vec<String>;

/// A variable name as a placeholder: `$name`, non-identifier characters replaced.
pub fn placeholder(name: &str) -> String {
    let mut out: String = name.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' }).collect();
    if !out.chars().next().map(|c| c.is_ascii_alphabetic() || c == '_').unwrap_or(false) {
        out = format!("v_{out}");
    }
    format!("${out}")
}

fn suffix(size: u16) -> String {
    if size == 0 {
        return String::new();
    }
    match size_suffix(size) {
        Some(s) => format!(".{s}"),
        None => format!(".{size}"),
    }
}

pub fn hex(value: i64) -> String {
    if value >= 0 {
        format!("{value:#x}")
    } else {
        format!("-{:#x}", value.unsigned_abs())
    }
}

fn is_pointer_op(op: Op) -> bool {
    matches!(op, Op::ConstPtr | Op::Import | Op::ExternPtr)
}

pub fn render_expr(f: &Function, e: ExprId, symbols: Option<SymbolLookup>) -> String {
    let op = f.op(e);
    let ops = f.operands(e);
    match op {
        Op::Var => {
            if let Some(v) = f.var_operand(e, 0) {
                return placeholder(f.var_name(v));
            }
        }
        Op::Const => {
            if let Some(v) = f.int_operand(e, 0) {
                return hex(v);
            }
        }
        _ if is_pointer_op(op) => {
            if let Some(v) = f.int_operand(e, 0) {
                if let Some(symbols) = symbols {
                    let mut names = symbols(v as u64);
                    if !names.is_empty() {
                        names.sort_by_key(|n| n.len());
                        return format!("\"{}\"", names[0]);
                    }
                }
                return hex(v);
            }
        }
        Op::Load => {
            if let Some(a) = f.sub(e, 0) {
                return format!("[{}]{}", render_expr(f, a, symbols), suffix(f.size(e)));
            }
        }
        Op::AddressOf => {
            if let Some(v) = f.var_operand(e, 0) {
                return format!("&{}", placeholder(f.var_name(v)));
            }
        }
        _ => {}
    }
    if let Some(infix) = op.infix() {
        if let (Some(Operand::Expr(a)), Some(Operand::Expr(b))) = (ops.first(), ops.get(1)) {
            if ops.len() == 2 {
                return format!("({} {} {})", render_expr(f, *a, symbols), infix, render_expr(f, *b, symbols));
            }
        }
    }
    let name = op.short_name().to_lowercase();
    let args: Vec<String> = ops.iter().map(|o| render_operand(f, *o, symbols)).collect();
    format!("{}{}({})", name, suffix(f.size(e)), args.join(", "))
}

fn render_operand(f: &Function, o: Operand, symbols: Option<SymbolLookup>) -> String {
    match o {
        Operand::Expr(e) => render_expr(f, e, symbols),
        Operand::Int(i) => hex(i),
        Operand::Var(v) => placeholder(f.var_name(v)),
        _ => "_".to_string(),
    }
}

/// How a block is named in the text: by the start index of the block it begins.
pub type LabelNames<'a> = &'a dyn Fn(u32) -> String;

pub fn render_stmt(f: &Function, index: u32, symbols: Option<SymbolLookup>) -> String {
    render_stmt_with(f, index, symbols, &|i: u32| format!("L{i}"))
}

/// Render one statement, naming branch targets with `label`.
pub fn render_stmt_with(f: &Function, index: u32, symbols: Option<SymbolLookup>, label: LabelNames) -> String {
    let e = f.instr(index);
    let op = f.op(e);
    match op {
        Op::SetVar => {
            if let (Some(v), Some(src)) = (f.var_operand(e, 0), f.sub(e, 1)) {
                return format!("{} = {}", placeholder(f.var_name(v)), render_expr(f, src, symbols));
            }
        }
        Op::Store => {
            if let (Some(d), Some(s)) = (f.sub(e, 0), f.sub(e, 1)) {
                return format!("[{}]{} = {}", render_expr(f, d, symbols), suffix(f.size(e)), render_expr(f, s, symbols));
            }
        }
        Op::If => {
            if let (Some(c), Some((t, fl))) = (f.sub(e, 0), f.if_targets(e)) {
                return format!("if ({}) then {} else {}", render_expr(f, c, symbols), label(t), label(fl));
            }
        }
        Op::Goto => {
            if let Some(t) = f.goto_target(e) {
                return format!("goto {}", label(t));
            }
        }
        Op::Ret => {
            let values: Vec<String> = f
                .list(f.operands(e)[0])
                .iter()
                .filter_map(|o| match o {
                    Operand::Expr(v) => Some(render_expr(f, *v, symbols)),
                    _ => None,
                })
                .collect();
            return format!("return {}", values.join(", ")).trim_end().to_string();
        }
        Op::Nop => return "nop".to_string(),
        Op::Call | Op::Tailcall => {
            let outputs: Vec<String> = f.call_outputs(e).iter().map(|v| placeholder(f.var_name(*v))).collect();
            let prefix = if outputs.is_empty() { String::new() } else { format!("{} = ", outputs.join(", ")) };
            let target = f.call_dest(e).map(|d| render_expr(f, d, symbols)).unwrap_or_default();
            let args: String = f.call_params(e).iter().map(|p| format!(", {}", render_expr(f, *p, symbols))).collect();
            return if op == Op::Call {
                format!("{prefix}call({target}{args})")
            } else {
                format!("return call({target}{args})")
            };
        }
        Op::Noret => return "noret()".to_string(),
        Op::Intrinsic => {
            let outputs: Vec<String> = f.vars_written(e).iter().map(|v| placeholder(f.var_name(*v))).collect();
            let prefix = if outputs.is_empty() { String::new() } else { format!("{} = ", outputs.join(", ")) };
            let name = match f.operand(e, 1) {
                Operand::Intrinsic(index) => f.intrinsic_name(index).map(str::to_string).unwrap_or_else(|| format!("intrinsic_{index}")),
                _ => "?".to_string(),
            };
            let args: String = f
                .list(f.operand(e, 2))
                .iter()
                .filter_map(|o| if let Operand::Expr(p) = o { Some(format!(", {}", render_expr(f, *p, symbols))) } else { None })
                .collect();
            return format!("{prefix}intrinsic(\"{name}\"{args})");
        }
        Op::TailcallUntyped
        | Op::CallUntyped
        | Op::Syscall
        | Op::SyscallUntyped
        | Op::JumpTo
        | Op::Assert => return format!("# unsupported: {}", op.name()),
        _ => {}
    }
    render_expr(f, e, symbols)
}

/// Render a whole function (or the instruction indices in `only`).  Blocks
/// other than the first are introduced by a `L<index>:` label so that
/// `if`/`goto` targets can be referenced; `texts` gives each instruction's
/// own text for the trailing comment (the host's rendering of it).
pub fn render_function(f: &Function, symbols: Option<SymbolLookup>, only: Option<&[u32]>, texts: Option<&[String]>) -> String {
    render_lines(f, symbols, only, texts, &|i: u32| format!("L{i}"), true)
}

/// The lines of [`render_function`], with the block names of `label`; the
/// first block gets a label line only with `label_first` (a full function
/// starting at its first instruction does not need one).
pub fn render_lines(
    f: &Function,
    symbols: Option<SymbolLookup>,
    only: Option<&[u32]>,
    texts: Option<&[String]>,
    label: LabelNames,
    label_first: bool,
) -> String {
    let mut lines: Vec<String> = Vec::new();
    let mut first = true;
    for block in &f.blocks {
        let indices: Vec<u32> = block.range().filter(|i| only.map(|o| o.contains(i)).unwrap_or(true)).collect();
        if indices.is_empty() {
            continue;
        }
        if !first || (label_first && (block.start != indices[0] || only.is_some())) {
            lines.push(format!("{}:", label(block.start)));
        }
        first = false;
        for i in &indices {
            let text = render_stmt_with(f, *i, symbols, label);
            let comment = texts.and_then(|t| t.get(*i as usize)).map(|t| t.as_str()).unwrap_or("");
            lines.push(format!("    {text}    # {i}: {comment}"));
        }
        // Blocks that fall through have no goto instruction; write one so the
        // text is a valid pattern (the matcher accepts a fall-through for it).
        let last = *indices.last().unwrap();
        if last == block.end - 1 && !f.instr_op(last).is_terminator() {
            let edges = &block.outgoing;
            if edges.len() == 1 && edges[0].kind.is_unconditional() {
                lines.push(format!("    goto {}    # fall through", label(f.block(edges[0].target).start)));
            }
        }
    }
    lines.join("\n") + "\n"
}
