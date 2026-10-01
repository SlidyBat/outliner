//! Printing a pattern back as text: what the drafter and the generaliser
//! produce, spelled so that the parser reads it back.

use crate::ops::size_suffix;
use crate::render::hex;

use super::{CallExpr, Dest, Expr, IntrinsicStmt, OpNode, Pattern, Stmt, SymbolRef, RET};

fn suffix(size: Option<u16>) -> String {
    match size {
        None | Some(0) => String::new(),
        Some(s) => match size_suffix(s) {
            Some(name) => format!(".{name}"),
            None => format!(".{s}"),
        },
    }
}

fn symbol(s: &SymbolRef) -> String {
    let plain = !s.name.is_empty()
        && s.name.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && s.name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == ':');
    if plain {
        s.name.clone()
    } else {
        format!("\"{}\"", s.name)
    }
}

fn constant(value: i128) -> String {
    if let Ok(v) = i64::try_from(value) {
        hex(v)
    } else {
        format!("{value:#x}")
    }
}

fn call(p: &Pattern, c: &CallExpr) -> String {
    let mut args: Vec<String> = c.args.iter().map(|a| format_expr(p, a)).collect();
    if c.variadic {
        args.push("...".to_string());
    }
    let target = match &c.target {
        Expr::Symbol(s) => symbol(s),
        other => format_expr(p, other),
    };
    let rest: String = args.iter().map(|a| format!(", {a}")).collect();
    format!("call({target}{rest})")
}

fn op_node(p: &Pattern, o: &OpNode) -> String {
    use crate::ops::Op;
    match o.op {
        Op::Load if o.args.len() == 1 => return format!("[{}]{}", format_expr(p, &o.args[0]), suffix(o.size)),
        Op::AddressOf if o.args.len() == 1 => {
            if let Expr::Placeholder(ph) = &o.args[0] {
                return format!("&${}", p.ph_name(*ph));
            }
        }
        _ => {}
    }
    if let Some(infix) = o.op.infix() {
        if o.args.len() == 2 && o.size.is_none() {
            return format!("({} {} {})", format_expr(p, &o.args[0]), infix, format_expr(p, &o.args[1]));
        }
    }
    let args: Vec<String> = o.args.iter().map(|a| format_expr(p, a)).collect();
    format!("{}{}({})", o.op.short_name().to_lowercase(), suffix(o.size), args.join(", "))
}

pub fn format_expr(p: &Pattern, e: &Expr) -> String {
    match e {
        Expr::Placeholder(ph) => format!("${}", p.ph_name(*ph)),
        Expr::Wildcard => "_".to_string(),
        Expr::Const(c) => constant(*c),
        Expr::Symbol(s) => symbol(s),
        Expr::Op(o) => op_node(p, o),
        Expr::Call(c) => call(p, c),
    }
}

fn dest(p: &Pattern, d: &Dest) -> String {
    match d {
        Dest::Ph(ph) => format!("${}", p.ph_name(*ph)),
        Dest::Wildcard => "_".to_string(),
    }
}

fn outputs(p: &Pattern, outs: &[Dest], extra: bool) -> String {
    let mut names: Vec<String> = outs.iter().map(|d| dest(p, d)).collect();
    if extra {
        names.push("...".to_string());
    }
    if names.is_empty() {
        String::new()
    } else {
        format!("{} = ", names.join(", "))
    }
}

fn intrinsic(p: &Pattern, c: &IntrinsicStmt) -> String {
    let mut args: Vec<String> = c.args.iter().map(|a| format_expr(p, a)).collect();
    if c.variadic {
        args.push("...".to_string());
    }
    let rest: String = args.iter().map(|a| format!(", {a}")).collect();
    format!("{}intrinsic(\"{}\"{rest})", outputs(p, &c.outputs, c.extra_outputs), c.name.name)
}

pub fn format_stmt(p: &Pattern, s: &Stmt) -> String {
    match s {
        Stmt::SetVar { dest: d, src } => format!("{} = {}", dest(p, d), format_expr(p, src)),
        Stmt::Store { size, dest: d, src } => format!("[{}]{} = {}", format_expr(p, d), suffix(*size), format_expr(p, src)),
        Stmt::Call(c) => {
            let expr = CallExpr { target: c.target.clone(), args: c.args.clone(), variadic: c.variadic };
            format!("{}{}", outputs(p, &c.outputs, c.extra_outputs), call(p, &expr))
        }
        Stmt::Intrinsic(c) => intrinsic(p, c),
        Stmt::Ret(values) => {
            let items: Vec<String> = values.iter().map(|v| format_expr(p, v)).collect();
            format!("return {}", items.join(", ")).trim_end().to_string()
        }
        Stmt::Nop => "nop".to_string(),
        Stmt::If { cond, t, f } => format!("if ({}) then {} else {}", format_expr(p, cond), p.label_name(*t), p.label_name(*f)),
        Stmt::Goto(l) => format!("goto {}", p.label_name(*l)),
        Stmt::Expr(e) => format_expr(p, e),
    }
}

/// The whole pattern as a chunk of text the parser reads back.
pub fn format_pattern(p: &Pattern) -> String {
    let mut lines: Vec<String> = Vec::new();
    if let Some(name) = &p.rules_name {
        lines.push(format!("rules: {name}"));
    }
    if let Some(sig) = &p.signature {
        lines.push(format!("signature: {sig}"));
    }
    for (id, t) in p.types.iter().enumerate() {
        if let Some(t) = t {
            lines.push(format!("${} : {}", p.names[id], t.text));
        }
    }
    if let Some(v) = &p.value {
        lines.push(format!("value: {}", format_expr(p, v)));
    }
    for (name, expr) in &p.results {
        if *name == RET {
            lines.push(format!("result: {}", format_expr(p, expr)));
        } else {
            lines.push(format!("result: ${} = {}", p.ph_name(*name), format_expr(p, expr)));
        }
    }
    if let Some(b) = &p.branch {
        lines.push(format!("branch: {}", format_expr(p, b)));
    }
    for rule in &p.rules {
        lines.push(format!("rewrite: {}", rule.text.trim()));
    }
    if !lines.is_empty() && p.blocks.iter().any(|b| !b.stmts.is_empty()) {
        lines.push(String::new());
    }
    for block in &p.blocks {
        if let Some(label) = block.label {
            lines.push(format!("{}:", p.label_name(label)));
        }
        for s in &block.stmts {
            lines.push(format!("    {}", format_stmt(p, s)));
        }
    }
    lines.join("\n") + "\n"
}
