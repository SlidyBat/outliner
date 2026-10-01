//! Parsing pattern text into a [`Pattern`].

use super::lexer::{tokenize, Kind, Token};
use super::{
    collect_placeholders, contains_call, image_store, Block, CallExpr, CallStmt, Dest, Expr, IntrinsicStmt, LabelId, OpNode,
    Pattern, PatternError, PhId, PhSet, Result, Rule, Stmt, SymbolRef, TypeConstraint, MAX_PLACEHOLDERS, RESULT_NAME,
};
use crate::ops::{size_from_suffix, Op};

const KEYWORDS: [&str; 14] = [
    "if", "then", "else", "goto", "call", "intrinsic", "return", "nop", "signature", "when", "rewrite", "rules", "result",
    "branch",
];

fn is_keyword(s: &str) -> bool {
    KEYWORDS.contains(&s)
}

/// A placeholder name table.
#[derive(Default)]
pub struct Names {
    pub list: Vec<String>,
}

impl Names {
    fn for_pattern() -> Names {
        Names { list: vec![RESULT_NAME.to_string()] }
    }

    fn intern(&mut self, name: &str, line: u32) -> Result<PhId> {
        if let Some(i) = self.list.iter().position(|n| n == name) {
            return Ok(PhId(i as u16));
        }
        if self.list.len() >= MAX_PLACEHOLDERS {
            return Err(PatternError(format!("line {line}: more than {MAX_PLACEHOLDERS} placeholders in one chunk")));
        }
        self.list.push(name.to_string());
        Ok(PhId(self.list.len() as u16 - 1))
    }
}

#[derive(Default)]
struct Labels {
    list: Vec<String>,
}

impl Labels {
    fn intern(&mut self, name: &str) -> LabelId {
        if let Some(i) = self.list.iter().position(|n| n == name) {
            return LabelId(i as u16);
        }
        self.list.push(name.to_string());
        LabelId(self.list.len() as u16 - 1)
    }
}

fn binary_op(text: &str) -> Option<(Op, u8)> {
    Some(match text {
        "|" => (Op::Or, 1),
        "^" => (Op::Xor, 2),
        "&" => (Op::And, 3),
        "==" => (Op::CmpE, 4),
        "!=" => (Op::CmpNe, 4),
        "s<" => (Op::CmpSlt, 5),
        "u<" => (Op::CmpUlt, 5),
        "s<=" => (Op::CmpSle, 5),
        "u<=" => (Op::CmpUle, 5),
        "s>" => (Op::CmpSgt, 5),
        "u>" => (Op::CmpUgt, 5),
        "s>=" => (Op::CmpSge, 5),
        "u>=" => (Op::CmpUge, 5),
        "<<" => (Op::Lsl, 6),
        ">>" => (Op::Lsr, 6),
        "s>>" => (Op::Asr, 6),
        "+" => (Op::Add, 7),
        "-" => (Op::Sub, 7),
        "*" => (Op::Mul, 8),
        "u/" => (Op::Divu, 8),
        "s/" => (Op::Divs, 8),
        "u%" => (Op::Modu, 8),
        "s%" => (Op::Mods, 8),
        _ => return None,
    })
}

const UNSIGNED_HINT: [&str; 6] = ["<", ">", "<=", ">=", "/", "%"];

struct Parser<'a> {
    toks: Vec<Token>,
    pos: usize,
    line: u32,
    names: &'a mut Names,
    labels: &'a mut Labels,
}

impl<'a> Parser<'a> {
    fn new(text: &str, line: u32, names: &'a mut Names, labels: &'a mut Labels) -> Result<Parser<'a>> {
        Ok(Parser { toks: tokenize(text, line)?, pos: 0, line, names, labels })
    }

    // -- helpers --------------------------------------------------------------
    fn peek(&self) -> &Token {
        &self.toks[self.pos.min(self.toks.len() - 1)]
    }

    fn peek_at(&self, offset: usize) -> &Token {
        &self.toks[(self.pos + offset).min(self.toks.len() - 1)]
    }

    fn next(&mut self) -> Token {
        let tok = self.toks[self.pos].clone();
        if tok.kind != Kind::Eof {
            self.pos += 1;
        }
        tok
    }

    fn at(&self, kind: Kind, text: Option<&str>) -> bool {
        let tok = self.peek();
        tok.kind == kind && text.map(|t| tok.text == t).unwrap_or(true)
    }

    fn at_op(&self, text: &str) -> bool {
        self.at(Kind::Op, Some(text))
    }

    fn at_ident(&self, text: &str) -> bool {
        self.at(Kind::Ident, Some(text))
    }

    fn expect(&mut self, kind: Kind, text: Option<&str>) -> Result<Token> {
        let tok = self.next();
        if tok.kind != kind || text.map(|t| tok.text != t).unwrap_or(false) {
            let want = text.map(|t| t.to_string()).unwrap_or_else(|| format!("{kind:?}").to_lowercase());
            let got = if tok.kind != Kind::Eof { tok.text.clone() } else { "end of line".to_string() };
            return Err(self.error(format!("expected '{want}' but found '{got}'")));
        }
        Ok(tok)
    }

    fn error(&self, msg: impl AsRef<str>) -> PatternError {
        PatternError(format!("line {}: {}", self.line, msg.as_ref()))
    }

    fn done(&self) -> Result<()> {
        if !self.at(Kind::Eof, None) {
            return Err(self.error(format!("unexpected '{}'", self.peek().text)));
        }
        Ok(())
    }

    fn ph(&mut self, name: &str) -> Result<PhId> {
        self.names.intern(name, self.line)
    }

    // -- statements -----------------------------------------------------------
    fn parse_statement(&mut self) -> Result<Stmt> {
        let tok = self.peek().clone();
        if tok.kind == Kind::Ident {
            match tok.text.as_str() {
                "if" => return self.parse_if(),
                "goto" => {
                    self.next();
                    let label = self.expect(Kind::Ident, None)?.text;
                    return Ok(Stmt::Goto(self.labels.intern(&label)));
                }
                "nop" => {
                    self.next();
                    return Ok(Stmt::Nop);
                }
                "return" => {
                    self.next();
                    let mut values = Vec::new();
                    if !self.at(Kind::Eof, None) {
                        values.push(self.parse_expr(1)?);
                        while self.at_op(",") {
                            self.next();
                            values.push(self.parse_expr(1)?);
                        }
                    }
                    return Ok(Stmt::Ret(values));
                }
                "call" => return Ok(Stmt::Call(self.parse_call(Vec::new(), false)?)),
                "intrinsic" => return Ok(Stmt::Intrinsic(self.parse_intrinsic(Vec::new(), false)?)),
                t if !is_keyword(t) && t != "_" => {
                    let expr = self.parse_primary()?;
                    return match expr {
                        Expr::Op(_) => Ok(Stmt::Expr(expr)),
                        _ => Err(self.error(format!("a bare name '{}' is not a statement", tok.text))),
                    };
                }
                _ => {}
            }
        }
        if tok.kind == Kind::Op && tok.text == "[" {
            self.next();
            let dest = self.parse_expr(1)?;
            self.expect(Kind::Op, Some("]"))?;
            let size = self.parse_size_suffix();
            self.expect(Kind::Op, Some("="))?;
            let src = self.parse_expr(1)?;
            return Ok(Stmt::Store { size, dest, src });
        }
        if tok.kind == Kind::Op && tok.text == "..." && self.peek_at(1).kind == Kind::Op && self.peek_at(1).text == "=" {
            // `... = call(f, args)`: the code's call may write any outputs, none of them wanted
            self.next();
            self.next();
            if self.at_ident("intrinsic") {
                return Ok(Stmt::Intrinsic(self.parse_intrinsic(Vec::new(), true)?));
            }
            if !self.at_ident("call") {
                return Err(self.error("'... =' must be followed by a call or an intrinsic"));
            }
            return Ok(Stmt::Call(self.parse_call(Vec::new(), true)?));
        }
        if tok.kind == Kind::Ph || (tok.kind == Kind::Ident && tok.text == "_") {
            let mut dests = vec![self.parse_dest()?];
            let mut extra = false;
            while self.at_op(",") {
                self.next();
                if self.at_op("...") {
                    self.next();
                    extra = true;
                    break;
                }
                dests.push(self.parse_dest()?);
            }
            self.expect(Kind::Op, Some("="))?;
            if self.at_ident("intrinsic") {
                return Ok(Stmt::Intrinsic(self.parse_intrinsic(dests, extra)?));
            }
            if self.at_ident("call") {
                let call = self.parse_call(dests.clone(), extra)?;
                if self.at(Kind::Eof, None) {
                    return Ok(Stmt::Call(call));
                }
                // `$p = call(...) - 1`: the call is the first operand of an expression
                if dests.len() != 1 || extra {
                    return Err(self.error("only a bare call can assign several outputs"));
                }
                let first = Expr::Call(Box::new(CallExpr { target: call.target, args: call.args, variadic: call.variadic }));
                let src = self.parse_binary(first, 1)?;
                return Ok(Stmt::SetVar { dest: dests[0], src });
            }
            if dests.len() != 1 || extra {
                return Err(self.error("only a call or an intrinsic can assign several outputs"));
            }
            let src = self.parse_expr(1)?;
            return Ok(Stmt::SetVar { dest: dests[0], src });
        }
        Err(self.error(format!("cannot parse statement starting at '{}'", tok.text)))
    }

    fn parse_dest(&mut self) -> Result<Dest> {
        let tok = self.next();
        match tok.kind {
            Kind::Ph => Ok(Dest::Ph(self.ph(&tok.text)?)),
            Kind::Ident if tok.text == "_" => Ok(Dest::Wildcard),
            _ => Err(self.error(format!("expected a $placeholder or _ as assignment target, found '{}'", tok.text))),
        }
    }

    fn parse_if(&mut self) -> Result<Stmt> {
        self.expect(Kind::Ident, Some("if"))?;
        self.expect(Kind::Op, Some("("))?;
        let cond = self.parse_expr(1)?;
        self.expect(Kind::Op, Some(")"))?;
        self.expect(Kind::Ident, Some("then"))?;
        let t = self.expect(Kind::Ident, None)?.text;
        self.expect(Kind::Ident, Some("else"))?;
        let f = self.expect(Kind::Ident, None)?.text;
        Ok(Stmt::If { cond, t: self.labels.intern(&t), f: self.labels.intern(&f) })
    }

    fn parse_call(&mut self, outputs: Vec<Dest>, extra_outputs: bool) -> Result<CallStmt> {
        self.expect(Kind::Ident, Some("call"))?;
        self.expect(Kind::Op, Some("("))?;
        let target = self.parse_expr(1)?;
        let mut args = Vec::new();
        let mut variadic = false;
        while self.at_op(",") {
            self.next();
            if self.at_op("...") {
                self.next();
                variadic = true;
                break;
            }
            args.push(self.parse_expr(1)?);
        }
        self.expect(Kind::Op, Some(")"))?;
        Ok(CallStmt { outputs, target, args, variadic, extra_outputs })
    }

    fn parse_intrinsic(&mut self, outputs: Vec<Dest>, extra_outputs: bool) -> Result<IntrinsicStmt> {
        self.expect(Kind::Ident, Some("intrinsic"))?;
        self.expect(Kind::Op, Some("("))?;
        let tok = self.next();
        if tok.kind != Kind::Str {
            return Err(self.error(format!("an intrinsic is named by a quoted string, found '{}'", tok.text)));
        }
        let name = SymbolRef { name: tok.text };
        let mut args = Vec::new();
        let mut variadic = false;
        while self.at_op(",") {
            self.next();
            if self.at_op("...") {
                self.next();
                variadic = true;
                break;
            }
            args.push(self.parse_expr(1)?);
        }
        self.expect(Kind::Op, Some(")"))?;
        Ok(IntrinsicStmt { outputs, name, args, variadic, extra_outputs })
    }

    // -- expressions ----------------------------------------------------------
    fn parse_expr(&mut self, min_prec: u8) -> Result<Expr> {
        let left = self.parse_unary()?;
        self.parse_binary(left, min_prec)
    }

    /// The rest of a binary expression whose first operand is `left`.
    fn parse_binary(&mut self, mut left: Expr, min_prec: u8) -> Result<Expr> {
        loop {
            let tok = self.peek().clone();
            if tok.kind != Kind::Op && tok.kind != Kind::Sop {
                break;
            }
            if UNSIGNED_HINT.contains(&tok.text.as_str()) {
                return Err(self.error(format!("'{0}' is ambiguous in MLIL; write s{0} or u{0}", tok.text)));
            }
            let Some((op, prec)) = binary_op(&tok.text) else { break };
            if prec < min_prec {
                break;
            }
            self.next();
            let right = self.parse_expr(prec + 1)?;
            left = Expr::op(op, None, vec![left, right]);
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<Expr> {
        let tok = self.peek().clone();
        if tok.kind == Kind::Op {
            match tok.text.as_str() {
                "-" => {
                    self.next();
                    if self.at(Kind::Num, None) {
                        let n = self.next();
                        return Ok(Expr::Const(-self.number(&n.text)?));
                    }
                    let inner = self.parse_unary()?;
                    return Ok(Expr::op(Op::Neg, None, vec![inner]));
                }
                "~" => {
                    self.next();
                    let inner = self.parse_unary()?;
                    return Ok(Expr::op(Op::Not, None, vec![inner]));
                }
                "&" => {
                    self.next();
                    let target = match self.parse_dest()? {
                        Dest::Ph(p) => Expr::Placeholder(p),
                        Dest::Wildcard => Expr::Wildcard,
                    };
                    return Ok(Expr::op(Op::AddressOf, None, vec![target]));
                }
                _ => {}
            }
        }
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> Result<Expr> {
        let tok = self.next();
        match tok.kind {
            Kind::Ph => Ok(Expr::Placeholder(self.ph(&tok.text)?)),
            Kind::Num => Ok(Expr::Const(self.number(&tok.text)?)),
            Kind::Str => Ok(Expr::Symbol(SymbolRef { name: tok.text })),
            Kind::Op if tok.text == "(" => {
                let inner = self.parse_expr(1)?;
                self.expect(Kind::Op, Some(")"))?;
                Ok(inner)
            }
            Kind::Op if tok.text == "[" => {
                let addr = self.parse_expr(1)?;
                self.expect(Kind::Op, Some("]"))?;
                let size = self.parse_size_suffix();
                Ok(Expr::op(Op::Load, size, vec![addr]))
            }
            Kind::Ident => {
                if tok.text == "_" {
                    return Ok(Expr::Wildcard);
                }
                if tok.text == "call" {
                    self.pos -= 1;
                    let c = self.parse_call(Vec::new(), false)?;
                    return Ok(Expr::Call(Box::new(CallExpr { target: c.target, args: c.args, variadic: c.variadic })));
                }
                if is_keyword(&tok.text) {
                    return Err(self.error(format!("unexpected keyword '{}' in expression", tok.text)));
                }
                let mut parts = vec![tok.text.clone()];
                while self.at_op(".") && matches!(self.peek_at(1).kind, Kind::Ident | Kind::Num) {
                    self.next();
                    parts.push(self.next().text);
                }
                if self.at_op("(") {
                    return self.parse_generic_op(parts);
                }
                Ok(Expr::Symbol(SymbolRef { name: parts.join(".") }))
            }
            _ => {
                let got = if tok.kind != Kind::Eof { tok.text } else { "end of line".to_string() };
                Err(self.error(format!("unexpected '{got}' in expression")))
            }
        }
    }

    fn parse_generic_op(&mut self, mut parts: Vec<String>) -> Result<Expr> {
        let mut size = None;
        if parts.len() > 1 {
            if let Some(s) = size_from_suffix(parts.last().unwrap()) {
                size = Some(s);
                parts.pop();
            }
        }
        let name = parts.join("_").to_uppercase();
        let op = match Op::from_name(&name) {
            Some(op) if op.is_pattern_op() => op,
            _ => return Err(self.error(format!("unknown MLIL operation '{}'", parts.join(".")))),
        };
        self.expect(Kind::Op, Some("("))?;
        let mut args = Vec::new();
        if !self.at_op(")") {
            args.push(self.parse_expr(1)?);
            while self.at_op(",") {
                self.next();
                args.push(self.parse_expr(1)?);
            }
        }
        self.expect(Kind::Op, Some(")"))?;
        Ok(Expr::Op(OpNode { op, size, args }))
    }

    fn parse_size_suffix(&mut self) -> Option<u16> {
        if self.at_op(".") && matches!(self.peek_at(1).kind, Kind::Ident | Kind::Num) {
            if let Some(size) = size_from_suffix(&self.peek_at(1).text) {
                self.next();
                self.next();
                return Some(size);
            }
        }
        None
    }

    fn number(&self, text: &str) -> Result<i128> {
        let value = if text.len() > 2 && (text.starts_with("0x") || text.starts_with("0X")) {
            i128::from_str_radix(&text[2..], 16)
        } else {
            text.parse::<i128>()
        };
        value.map_err(|_| self.error(format!("bad number '{text}'")))
    }
}

// --------------------------------------------------------------------------- lines

/// `name: value` at the start of a line; the value, trimmed, when it is not empty.
fn directive<'a>(line: &'a str, name: &str) -> Option<&'a str> {
    let t = line.trim_start();
    let rest = t.strip_prefix(name)?;
    let rest = rest.trim_start().strip_prefix(':')?;
    let value = rest.trim();
    if value.is_empty() {
        None
    } else {
        Some(value)
    }
}

pub(crate) fn strip_comment(line: &str) -> String {
    let mut out = String::new();
    let mut in_str = false;
    for (i, c) in line.char_indices() {
        if c == '"' {
            in_str = !in_str;
        } else if !in_str && (c == '#' || line[i..].starts_with("//")) {
            break;
        }
        out.push(c);
    }
    out
}

fn ident_prefix(s: &str) -> Option<&str> {
    let b = s.as_bytes();
    if b.is_empty() || !(b[0].is_ascii_alphabetic() || b[0] == b'_') {
        return None;
    }
    let end = b.iter().position(|c| !(c.is_ascii_alphanumeric() || *c == b'_')).unwrap_or(b.len());
    Some(&s[..end])
}

/// `$name : type` (a type constraint), or None.
fn type_line(line: &str) -> Option<(&str, &str)> {
    let t = line.trim_start();
    let rest = t.strip_prefix('$')?;
    let name = ident_prefix(rest)?;
    let after = rest[name.len()..].trim_start();
    let value = after.strip_prefix(':')?.trim();
    if value.is_empty() {
        return None;
    }
    // `$x = y:z` is a statement, not a constraint
    if line.split_once(':').map(|(head, _)| head.contains('=')).unwrap_or(false) {
        return None;
    }
    Some((name, value))
}

/// `label: rest`, or None.
fn label_line(stmt: &str) -> Option<(&str, &str)> {
    let t = stmt.trim_start();
    let name = ident_prefix(t)?;
    let after = t[name.len()..].trim_start();
    let rest = after.strip_prefix(':')?;
    Some((name, rest.trim()))
}

/// `result: [$name =] expr`: the target placeholder (None: `$ret`) and the expression text.
fn result_target(value: &str) -> (Option<&str>, &str) {
    if let Some(rest) = value.strip_prefix('$') {
        if let Some(name) = ident_prefix(rest) {
            let after = rest[name.len()..].trim_start();
            if let Some(expr) = after.strip_prefix('=') {
                if !expr.starts_with('=') {
                    return (Some(name), expr.trim());
                }
            }
        }
    }
    (None, value)
}

fn parse_rule(text: &str, line: u32) -> Result<Rule> {
    let mut names = Names::default();
    let mut labels = Labels::default();
    let (lhs, rhs, when) = {
        let mut p = Parser::new(text, line, &mut names, &mut labels)?;
        let lhs = p.parse_expr(1)?;
        p.expect(Kind::Op, Some("=>"))?;
        let rhs = p.parse_expr(1)?;
        let mut when = None;
        if p.at_ident("when") {
            p.next();
            when = Some(p.parse_expr(1)?);
        }
        p.done()?;
        (lhs, rhs, when)
    };
    if !matches!(lhs, Expr::Op(_)) {
        return Err(PatternError(format!("line {line}: the left side of a rewrite rule must be an operation")));
    }
    let mut lhs_names = PhSet::default();
    collect_placeholders(&lhs, &mut lhs_names);
    for (label, part) in [("right side", Some(&rhs)), ("condition", when.as_ref())] {
        let Some(part) = part else { continue };
        let mut found = PhSet::default();
        collect_placeholders(part, &mut found);
        if let Some(unknown) = found.iter().find(|p| !lhs_names.contains(*p)) {
            return Err(PatternError(format!(
                "line {line}: placeholder ${} in the {label} does not occur on the left side",
                names.list[unknown.0 as usize]
            )));
        }
        if contains_call(part) {
            return Err(PatternError(format!("line {line}: call(...) cannot be used on the right side of a rule")));
        }
    }
    Ok(Rule { lhs, rhs, when, text: text.to_string(), names: names.list })
}

fn parse_expr_text(text: &str, line: u32, names: &mut Names, labels: &mut Labels) -> Result<Expr> {
    let mut p = Parser::new(text, line, names, labels)?;
    let expr = p.parse_expr(1)?;
    p.done()?;
    Ok(expr)
}

/// Parse pattern syntax without the structural rules a pattern must obey: what
/// *Show Function As Pattern Text* prints for a whole function (blocks ending in
/// returns, labels in any order) parses this way, so rendered functions can be
/// replayed as test fakes.
pub fn parse_function_text(text: &str) -> Result<Pattern> {
    let mut names = Names::for_pattern();
    let mut labels = Labels::default();
    let mut blocks: Vec<Block> = vec![Block { label: None, stmts: Vec::new(), line: 1, stmt_lines: Vec::new() }];
    let mut types: Vec<(PhId, TypeConstraint)> = Vec::new();
    let mut signature: Option<String> = None;
    let mut value: Option<Expr> = None;
    let mut results: Vec<(PhId, Expr)> = Vec::new();
    let mut branch: Option<Expr> = None;
    let mut rules: Vec<Rule> = Vec::new();
    let mut rules_name: Option<String> = None;

    for (k, raw) in text.lines().enumerate() {
        let lineno = k as u32 + 1;
        let line = strip_comment(raw);
        if let Some(rest) = directive(&line, "rewrite") {
            rules.push(parse_rule(rest, lineno)?);
            continue;
        }
        if let Some(rest) = directive(&line, "rules") {
            rules_name = Some(rest.to_string());
            continue;
        }
        if let Some(rest) = directive(&line, "signature") {
            if signature.is_some() {
                return Err(PatternError(format!("line {lineno}: duplicate signature directive")));
            }
            signature = Some(rest.to_string());
            continue;
        }
        if let Some(rest) = directive(&line, "value") {
            if value.is_some() {
                return Err(PatternError(format!("line {lineno}: duplicate value directive")));
            }
            value = Some(parse_expr_text(rest, lineno, &mut names, &mut labels)?);
            continue;
        }
        if let Some(rest) = directive(&line, "result") {
            let (target, expr_text) = result_target(rest);
            let target = names.intern(target.unwrap_or(RESULT_NAME), lineno)?;
            if results.iter().any(|(existing, _)| *existing == target) {
                return Err(PatternError(format!(
                    "line {lineno}: duplicate result line for ${}",
                    names.list[target.0 as usize]
                )));
            }
            let expr = parse_expr_text(expr_text, lineno, &mut names, &mut labels)?;
            results.push((target, expr));
            continue;
        }
        if let Some(rest) = directive(&line, "branch") {
            if branch.is_some() {
                return Err(PatternError(format!("line {lineno}: duplicate branch directive")));
            }
            branch = Some(parse_expr_text(rest, lineno, &mut names, &mut labels)?);
            continue;
        }
        if let Some((name, type_text)) = type_line(&line) {
            let id = names.intern(name, lineno)?;
            if types.iter().any(|(existing, _)| *existing == id) {
                return Err(PatternError(format!("line {lineno}: duplicate type constraint for ${name}")));
            }
            types.push((id, TypeConstraint::new(type_text)));
            continue;
        }
        for part in line.split(';') {
            let mut stmt_text = part.trim();
            if stmt_text.is_empty() {
                continue;
            }
            if let Some((label, rest)) = label_line(stmt_text) {
                if !is_keyword(label) {
                    let id = labels.intern(label);
                    if blocks.iter().any(|b| b.label == Some(id)) {
                        return Err(PatternError(format!("line {lineno}: duplicate label '{label}'")));
                    }
                    if blocks.len() == 1 && blocks[0].label.is_none() && blocks[0].stmts.is_empty() {
                        // A label before any statement names the first block, so a
                        // loop may branch back to the pattern's entry.
                        blocks[0].label = Some(id);
                        blocks[0].line = lineno;
                    } else {
                        blocks.push(Block { label: Some(id), stmts: Vec::new(), line: lineno, stmt_lines: Vec::new() });
                    }
                    stmt_text = rest;
                    if stmt_text.is_empty() {
                        continue;
                    }
                }
            }
            let stmt = {
                let mut p = Parser::new(stmt_text, lineno, &mut names, &mut labels)?;
                let stmt = p.parse_statement()?;
                p.done()?;
                stmt
            };
            let block = blocks.last_mut().unwrap();
            block.stmts.push(stmt);
            block.stmt_lines.push(lineno);
        }
    }

    let mut type_table: Vec<Option<TypeConstraint>> = vec![None; names.list.len()];
    for (id, t) in types {
        type_table[id.0 as usize] = Some(t);
    }
    Ok(Pattern::new(
        blocks,
        names.list,
        labels.list,
        type_table,
        signature,
        text.to_string(),
        value,
        results,
        branch,
        rules,
        rules_name,
    ))
}

/// Parse pattern text into a [`Pattern`].
pub fn parse_pattern(text: &str) -> Result<Pattern> {
    let pattern = parse_function_text(text)?;
    validate_structure(&pattern)?;
    Ok(pattern)
}

fn validate_structure(pattern: &Pattern) -> Result<()> {
    let e = |msg: String| Err(PatternError(msg));
    let blocks = &pattern.blocks;
    if !pattern.rules.is_empty() || pattern.rules_name.is_some() {
        if pattern.rules.is_empty() {
            return e("a 'rules:' chunk needs at least one 'rewrite:' line".into());
        }
        if pattern.signature.is_some()
            || pattern.value.is_some()
            || pattern.types.iter().any(|t| t.is_some())
            || blocks.iter().any(|b| !b.stmts.is_empty())
            || blocks.len() > 1
        {
            return e("rewrite rules must be in a chunk of their own, without a signature or statements".into());
        }
        return Ok(());
    }
    if let Some(value) = &pattern.value {
        if blocks.iter().any(|b| !b.stmts.is_empty()) || blocks.len() > 1 {
            return e("a 'value:' pattern cannot also contain statements".into());
        }
        if !pattern.results.is_empty() {
            return e("a 'value:' pattern cannot have a 'result:' line".into());
        }
        if !matches!(value, Expr::Op(_) | Expr::Call(_)) {
            return e("the value of a 'value:' pattern must be an operation or a call, not a bare name".into());
        }
        return Ok(());
    }
    for block in blocks {
        for stmt in &block.stmts {
            image_store(stmt)?; // a malformed byte image is an error
        }
    }
    if !pattern.results.is_empty() {
        let mut seen_call: Option<&CallExpr> = None;
        for (line_name, expr) in &pattern.results {
            let mut calls = Vec::new();
            super::collect_calls(expr, &mut calls);
            if calls.len() > 1 {
                return e(format!("the 'result:' line for ${} mentions more than one call", pattern.ph_name(*line_name)));
            }
            if let Some(call) = calls.first() {
                if !matches!(call.target, Expr::Symbol(_)) || call.variadic {
                    return e("the call in 'result:' must name this pattern's function and take fixed arguments".into());
                }
                if let Some(seen) = seen_call {
                    if seen != *call {
                        return e("every 'result:' line must spell the same call".into());
                    }
                }
                seen_call = Some(call);
            } else {
                let mut names = PhSet::default();
                collect_placeholders(expr, &mut names);
                if !names.contains(super::RET) {
                    return e(format!(
                        "the 'result:' line for ${} must mention the call or ${RESULT_NAME}",
                        pattern.ph_name(*line_name)
                    ));
                }
            }
        }
        if seen_call.is_none() {
            return e("at least one 'result:' line must contain the call to this pattern's own function, such as \
                      'result: $v = call(<function>, <arguments>) != 1'; further lines may use $ret for the call's value"
                .into());
        }
    }
    if blocks[0].stmts.is_empty() {
        return e("the pattern must start with at least one statement".into());
    }
    let defined = pattern.defined_labels();
    for label in &defined {
        if is_keyword(pattern.label_name(*label)) {
            return e(format!("'{}' cannot be used as a label", pattern.label_name(*label)));
        }
    }
    let mut external: Vec<LabelId> = Vec::new();
    for (i, block) in blocks.iter().enumerate() {
        let is_last = i == blocks.len() - 1;
        for (j, stmt) in block.stmts.iter().enumerate() {
            if matches!(stmt, Stmt::If { .. } | Stmt::Goto(_)) && j != block.stmts.len() - 1 {
                return e(format!("'if'/'goto' must be the last statement of a block (line {})", block.line));
            }
            if let Stmt::If { t, f, .. } = stmt {
                for target in [*t, *f] {
                    if !defined.contains(&target) {
                        // With branch:, an if may leave the pattern on one side.
                        if pattern.branch.is_some() {
                            if !external.contains(&target) {
                                external.push(target);
                            }
                        } else {
                            return e(format!("undefined label '{}'", pattern.label_name(target)));
                        }
                    }
                }
            }
            if let Stmt::Goto(l) = stmt {
                if !defined.contains(l) {
                    return e(format!("undefined label '{}'", pattern.label_name(*l)));
                }
            }
        }
        let term = block.terminator();
        if is_last && term.is_some() && !matches!(term, Some(Stmt::Ret(_))) {
            return e("the last block of a pattern must not end with 'if', 'goto' or 'noret()'; leave the following code out of the pattern instead".into());
        }
        if !is_last && term.is_none() {
            let where_ = match block.label {
                Some(l) => format!("block '{}'", pattern.label_name(l)),
                None => "the entry block".to_string(),
            };
            return e(format!("{where_} must end with 'if', 'goto', 'return' or 'noret()' because more blocks follow"));
        }
    }
    if pattern.branch.is_some() && (pattern.exit_branch().is_none() || external.len() != 1 || blocks.len() < 2) {
        return e("'branch:' needs exactly one label with no block, where the pattern's 'if' statements leave it; after the call the branch condition decides between that label and the code after the pattern's last block".into());
    }
    let mut referenced: Vec<LabelId> = Vec::new();
    for block in blocks {
        match block.terminator() {
            Some(Stmt::If { t, f, .. }) => {
                referenced.push(*t);
                referenced.push(*f);
            }
            Some(Stmt::Goto(l)) => referenced.push(*l),
            _ => {}
        }
    }
    for label in &defined {
        if !referenced.contains(label) {
            return e(format!("label '{}' is never targeted by an 'if' or 'goto'", pattern.label_name(*label)));
        }
    }
    Ok(())
}
