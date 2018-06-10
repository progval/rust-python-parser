use super::super::ast::*;

fn comma_join<'a, T2: ToString, T: IntoIterator<Item=T2>>(i: T) -> String {
    let mut i = i.into_iter();
    let mut s: String = i.next().map(|s| s.to_string()).unwrap_or("".to_string());
    for s2 in i {
        s.push_str(", ");
        s.push_str(&s2.to_string()[..]);
    }
    s
}

fn space_join<'a, T2: ToString, T: IntoIterator<Item=T2>>(i: T) -> String {
    let mut i = i.into_iter();
    let mut s: String = i.next().map(|s| s.to_string()).unwrap_or("".to_string());
    for s2 in i {
        s.push_str(" ");
        s.push_str(&s2.to_string()[..]);
    }
    s
}

fn dot_join<'a, T2: ToString, T: IntoIterator<Item=T2>>(i: T) -> String {
    let mut i = i.into_iter();
    let mut s: String = i.next().map(|s| s.to_string()).unwrap_or("".to_string());
    for s2 in i {
        s.push_str(".");
        s.push_str(&s2.to_string()[..]);
    }
    s
}

pub fn format_module(stmts: &[Statement]) -> String {
    let mut s = "".to_string();
    for stmt in stmts {
        s.push_str(&format_statement(0, &stmt)[..])
    }
    s
}

fn push_indent(indent: usize, s: &mut String) {
    for _ in 0..indent {
        s.push_str(" ")
    }
}

fn format_statement(indent: usize, stmt: &Statement) -> String {
    let mut s = "".to_string();
    push_indent(indent, &mut s);
    match *stmt {
        Statement::Pass => s.push_str("pass\n"),
        Statement::Del(ref exprs) => {
            s.push_str("del ");
            s.push_str(&comma_join(exprs.iter().map(format_expr)));
            s.push_str("\n");
        },
        Statement::Break => s.push_str("break\n"),
        Statement::Continue => s.push_str("continue\n"),
        Statement::Return(ref exprs) => {
            s.push_str("return ");
            s.push_str(&comma_join(exprs.iter().map(format_expr)));
            s.push_str("\n");
        },
        Statement::RaiseExcFrom(ref exc, ref from_exc) => {
            s.push_str("raise ");
            s.push_str(&format_expr(exc));
            s.push_str(" from ");
            s.push_str(&format_expr(from_exc));
            s.push_str("\n");
        },
        Statement::RaiseExc(ref exc) => {
            s.push_str("raise ");
            s.push_str(&format_expr(exc));
            s.push_str("\n");
        },
        Statement::Raise => {
            s.push_str("raise\n");
        },
        Statement::Global(ref names) => {
            s.push_str("global ");
            s.push_str(&comma_join(names));
            s.push_str("\n");
        },
        Statement::Nonlocal(ref names) => {
            s.push_str("nonlocal ");
            s.push_str(&comma_join(names));
            s.push_str("\n");
        },
        Statement::Assert(ref expr, ref msg) => {
            s.push_str("assert ");
            s.push_str(&format_expr(expr));
            if let Some(msg) = msg {
                s.push_str(", ");
                s.push_str(&format_expr(msg));
            }
            s.push_str("\n");
        },
        Statement::Import(ref imp) => {
            s.push_str(&format_import(imp));
            s.push_str("\n");
        },
        Statement::Expressions(ref exprs) => {
            s.push_str(&comma_join(exprs.iter().map(format_expr)));
            s.push_str("\n");
        },
        Statement::Assignment(ref lhs, ref rhs) => {
            s.push_str(&comma_join(lhs.iter().map(format_expr)));
            for part in rhs {
                s.push_str(" = ");
                s.push_str(&comma_join(part.iter().map(format_expr)));
            }
            s.push_str("\n");
        },
        Statement::TypedAssignment(ref lhs, ref typed, ref rhs) => {
            s.push_str(&format!("{}:{} = {}\n",
                comma_join(lhs.iter().map(format_expr)),
                format_expr(typed),
                comma_join(rhs.iter().map(format_expr))));
        },
        Statement::AugmentedAssignment(ref lhs, op, ref rhs) => {
            s.push_str(&format!("{} {} {}\n",
                comma_join(lhs.iter().map(format_expr)),
                op,
                comma_join(rhs.iter().map(format_expr))));
        },
        Statement::Compound(ref stmt) => s.push_str(&format_compound_statement(indent, stmt)),
    }
    s
}

fn format_compound_statement(indent: usize, stmt: &CompoundStatement) -> String {
    match stmt {
        CompoundStatement::If(ref cond_blocks, ref else_block) => {
            let mut s = String::new();
            let mut first = true;
            for (ref cond, ref block) in cond_blocks {
                if first {
                    s.push_str("if ");
                    s.push_str(&format_expr(cond));
                    s.push_str(":\n");
                    s.push_str(&format_block(indent+4, block));
                    first = false;
                }
                else {
                    push_indent(indent, &mut s);
                    s.push_str("elif ");
                    s.push_str(&format_expr(cond));
                    s.push_str(":\n");
                    s.push_str(&format_block(indent+4, block));
                }
            }
            if let Some(block) = else_block {
                push_indent(indent, &mut s);
                s.push_str("else:\n");
                s.push_str(&format_block(indent+4, block));
            }
            s
        },
        CompoundStatement::For { async, ref item, ref iterator, ref for_block, ref else_block } => {
            let mut s = String::new();
            if *async {
                s.push_str("async ");
            }
            s.push_str("for ");
            s.push_str(&comma_join(item.iter().map(format_expr)));
            s.push_str(" in ");
            s.push_str(&comma_join(iterator.iter().map(format_expr)));
            s.push_str(":\n");
            s.push_str(&format_block(indent+4, for_block));

            if let Some(block) = else_block {
                push_indent(indent, &mut s);
                s.push_str("else:\n");
                s.push_str(&format_block(indent+4, block));
            }
            s
        }
        CompoundStatement::While(ref cond, ref block, ref else_block) => {
            let mut s = String::new();
            s.push_str("while ");
            s.push_str(&format_expr(cond));
            s.push_str(":\n");
            s.push_str(&format_block(indent+4, block));

            if let Some(block) = else_block {
                push_indent(indent, &mut s);
                s.push_str("else:\n");
                s.push_str(&format_block(indent+4, block));
            }
            s
        },
        CompoundStatement::Try(Try { ref try_block, ref except_clauses, ref last_except, ref else_block, ref finally_block }) => {
            let mut s = String::new();

            s.push_str("try:\n");
            s.push_str(&format_block(indent+4, try_block));

            for (ref guard, ref name, ref block) in except_clauses {
                push_indent(indent, &mut s);
                s.push_str("except ");
                s.push_str(&format_expr(guard));
                if let Some(name) = name {
                    s.push_str(" as ");
                    s.push_str(name);
                }
                s.push_str(":\n");
                s.push_str(&format_block(indent+4, block));
            }
            if last_except.len() > 0 {
                push_indent(indent, &mut s);
                s.push_str("except:\n");
                s.push_str(&format_block(indent+4, last_except));
            }
            if else_block.len() > 0 {
                push_indent(indent, &mut s);
                s.push_str("else:\n");
                s.push_str(&format_block(indent+4, else_block));
            }
            if finally_block.len() > 0 {
                push_indent(indent, &mut s);
                s.push_str("finally:\n");
                s.push_str(&format_block(indent+4, finally_block));
            }
            s
        },
        CompoundStatement::With(ref contexts, ref block) => {
            let mut s = String::new();

            s.push_str("with ");
            assert!(contexts.len() > 0);
            let mut first = true;
            for (ctx, as_what) in contexts {
                if first {
                    first = false;
                }
                else {
                    s.push_str(", ");
                }
                s.push_str(&format_expr(ctx));
                if let Some(ref e) = as_what {
                    s.push_str(" as ");
                    s.push_str(&format_expr(e));
                }
            }
            s.push_str(":\n");
            s.push_str(&format_block(indent+4, block));
            s
        }
        CompoundStatement::Funcdef(ref funcdef) => format_funcdef(indent, funcdef),
        CompoundStatement::Classdef(ref classdef) => format_classdef(indent, classdef),
    }
}

fn format_decorators(indent: usize, decorators: &Vec<Decorator>) -> String {
    let mut s = String::new();
    for Decorator { ref name, ref args } in decorators {
        push_indent(indent, &mut s);
        s.push_str("@");
        s.push_str(&dot_join(name));
        if let Some(ref arglist) = args {
            s.push_str(&format_args(arglist));
        }
        s.push_str("\n");
    }
    s
}

fn format_funcdef(indent: usize, funcdef: &Funcdef) -> String {
    let Funcdef { async, ref decorators, ref name, ref parameters, ref return_type, ref code } = funcdef;
    let mut s = "\n".to_string();
    s.push_str(&format_decorators(indent, decorators));
    push_indent(indent, &mut s);
    if *async {
        s.push_str("async ");
    }
    s.push_str("def ");
    s.push_str(name);
    s.push_str("(");
    s.push_str(&format_typed_params(parameters));
    s.push_str(")");
    if let Some(ref ret) = return_type {
        s.push_str(" -> ");
        s.push_str(&format_expr(ret));
    }
    s.push_str(":\n");
    s.push_str(&format_block(indent+4, code));
    s.push_str("\n");
    s
}

fn format_classdef(indent: usize, classdef: &Classdef) -> String {
    let Classdef { ref decorators, ref name, ref arguments, ref code } = classdef;
    let mut s = "\n".to_string();
    s.push_str(&format_decorators(indent, decorators));
    push_indent(indent, &mut s);
    s.push_str("class ");
    s.push_str(name);
    s.push_str("(");
    s.push_str(&format_args(arguments));
    s.push_str(")");
    s.push_str(":\n");
    s.push_str(&format_block(indent+4, code));
    s.push_str("\n");
    s
}

fn format_block(indent: usize, stmts: &Vec<Statement>) -> String {
    let mut s = String::new();
    for stmt in stmts {
        s.push_str(&format_statement(indent, stmt));
    }
    s
}

fn format_dictitem(si: &DictItem) -> String {
    match si {
        DictItem::Unique(ref e1, ref e2) => format!("{}:{}", format_expr(e1), format_expr(e2)),
        DictItem::Star(ref e) => format!("**{}", format_expr(e)),
    }
}

fn format_setitem(si: &SetItem) -> String {
    match si {
        SetItem::Unique(ref e) => format_expr(e),
        SetItem::Star(ref e) => format!("*{}", format_expr(e)),
    }
}

fn format_pos_arg(arg: &Argument<Expression>) -> String {
    match *arg {
        Argument::Normal(ref e) => format_expr(e),
        Argument::Star(ref e) => format!("*{}", format_expr(e)),
    }
}

fn format_kw_arg(arg: &Argument<(Name, Expression)>) -> String {
    match *arg {
        Argument::Normal((ref n, ref e)) => format!("{}={}", n, format_expr(e)),
        Argument::Star(ref e) => format!("**{}", format_expr(e)),
    }
}

fn format_args(args: &Arglist) -> String {
    let Arglist { ref positional_args, ref keyword_args } = *args;
    let mut s = String::new();
    s.push_str(&comma_join(positional_args.iter().map(format_pos_arg)));
    if positional_args.len() > 0 && keyword_args.len() > 0 {
        s.push_str(", ");
    }
    s.push_str(&comma_join(keyword_args.iter().map(format_kw_arg)));
    s
}

fn format_typed_params(param: &TypedArgsList) -> String {
    let TypedArgsList { ref positional_args, ref star_args, ref keyword_args, ref star_kwargs } = *param;
    let mut chunks = Vec::new();

    chunks.extend(positional_args.iter().map(format_typed_param));

    match star_args {
        StarParams::No => (),
        StarParams::Anonymous => chunks.push("*".to_string()),
        StarParams::Named((ref name, None)) => chunks.push(format!("*{}", name)),
        StarParams::Named((ref name, Some(ref typed))) =>
            chunks.push(format!("*{}:{}", name, format_expr(typed))),
    }

    chunks.extend(keyword_args.iter().map(format_typed_param));

    if let Some((name, typed)) = star_kwargs {
        if let Some(typed) = typed {
            chunks.push(format!("**{}:{}", name, format_expr(typed)))
        }
        else {
            chunks.push(format!("**{}", name));
        }
    }

    comma_join(chunks)
}

fn format_typed_param(param: &(Name, Option<Expression>, Option<Expression>)) -> String {
    let (name, typed, value) = param;
    let mut s = name.to_string();
    if let Some(ref typed) = typed {
        s.push_str(":");
        s.push_str(&format_expr(typed));
    }
    if let Some(ref value) = value {
        s.push_str("=");
        s.push_str(&format_expr(value));
    }
    s
}

fn format_untyped_params(param: &UntypedArgsList) -> String {
    let UntypedArgsList { ref positional_args, ref star_args, ref keyword_args, ref star_kwargs } = *param;
    let mut s = String::new();

    s.push_str(&comma_join(positional_args.iter().map(format_untyped_param)));
    if positional_args.len() > 0 {
        s.push_str(", ");
    }

    match star_args {
        StarParams::No => (),
        StarParams::Anonymous => s.push_str("*, "),
        StarParams::Named(ref name) => {
            s.push_str(name);
        },
    }

    s.push_str(&comma_join(keyword_args.iter().map(format_untyped_param)));
    if keyword_args.len() > 0 {
        s.push_str(", ");
    }

    if let Some(name) = star_kwargs {
        s.push_str("**");
        s.push_str(name);
        s.push_str(", ");
    }

    s
}

fn format_untyped_param(param: &(Name, Option<Expression>)) -> String {
    let (name, value) = param;
    let mut s = name.to_string();
    if let Some(ref value) = value {
        s.push_str("=");
        s.push_str(&format_expr(value));
    }
    s
}

fn format_subscript(sub: &Subscript) -> String {
    match *sub {
        Subscript::Simple(ref e) => format_expr(e),
        Subscript::Double(ref e1, ref e2) => format!("{}:{}",
            e1.clone().map(|e| format_expr(&e)).unwrap_or_default(),
            e2.clone().map(|e| format_expr(&e)).unwrap_or_default(),
        ),
        Subscript::Triple(ref e1, ref e2, ref e3) => format!("{}:{}:{}",
            e1.clone().map(|e| format_expr(&e)).unwrap_or_default(),
            e2.clone().map(|e| format_expr(&e)).unwrap_or_default(),
            e3.clone().map(|e| format_expr(&e)).unwrap_or_default(),
        ),
    }
}

fn format_comp(comp: &ComprehensionChunk) -> String {
    match *comp {
        ComprehensionChunk::If { ref cond } => format!("if {}", format_expr(cond)),
        ComprehensionChunk::For { async, ref item, ref iterator } => format!("{}for {} in {}",
            if async { "async " } else { "" },
            comma_join(item.iter().map(format_expr)),
            format_expr(iterator)
        ),
    }
}

fn format_float(n: f64) -> String {
    let mut s = n.to_string();
    if s.find('.').is_none() {
        s.push_str(".");
    }
    s
}

fn format_expr(e: &Expression) -> String {
    match e {
        Expression::Ellipsis => "...".to_string(),
        Expression::None => "None".to_string(),
        Expression::True => "True".to_string(),
        Expression::False => "False".to_string(),
        Expression::Name(ref n) => n.to_string(),
        Expression::Int(ref n) => n.to_string(),
        Expression::ImaginaryInt(ref n) => format!("{}j", n),
        Expression::Float(ref n) => format_float(*n),
        Expression::ImaginaryFloat(ref n) => format!("{}j", format_float(*n)),
        Expression::String(ref v) => {
            space_join(v.iter().map(|PyString { prefix, content }|
                format!("{}\"{}\"", prefix.to_ascii_lowercase().replace("r", ""), content.chars().map(|c| match c {
                    '\r' => "\\r".to_string(),
                    '\n' => "\\n".to_string(),
                    '\t' => "\\t".to_string(),
                    '\\' => "\\\\".to_string(),
                    '"' => "\\\"".to_string(),
                    '\x20'...'\x7e' => c.to_string(),
                    '\x00'...'\x1f' | '\x7f' | '\u{80}'...'\u{ff}' => format!("\\x{:02x}", c as u8),
                    '\u{100}'...'\u{ffff}' => format!("\\u{:04x}", c as u16),
                    '\u{10000}'...'\u{10ffff}' => format!("\\U{:08x}", c as u32),
                    _ => unreachable!(),
                }).collect::<Vec<_>>()[..].concat())
            ))
        },
        Expression::Bytes(ref content) => {
            format!("b\"{}\"", content.iter().map(|b| match b {
                b'\r' => "\\r".to_string(),
                b'\n' => "\\n".to_string(),
                b'\t' => "\\t".to_string(),
                b'\\' => "\\\\".to_string(),
                b'"' => "\\\"".to_string(),
                0x20...0x7e => (*b as char).to_string(),
                0x00...0x1f | 0x7f | 0x80...0xff => format!("\\x{:02x}", b),
                _ => unreachable!(), // waiting for https://github.com/rust-lang/rust/pull/50912
            }).collect::<Vec<_>>()[..].concat())
        },

        Expression::DictLiteral(ref v) =>
            format!("{{{}}}", comma_join(v.iter().map(format_dictitem))),
        Expression::SetLiteral(ref v) =>
            format!("{{{}}}", comma_join(v.iter().map(format_setitem))),
        Expression::ListLiteral(ref v) =>
            format!("[{}]", comma_join(v.iter().map(format_setitem))),
        Expression::TupleLiteral(ref v) => {
            match v.len() {
                0 => "()".to_string(),
                1 => format!("({},)", format_setitem(&v[0])),
                _ => format!("({})", comma_join(v.iter().map(format_setitem))),
            }
        },

        Expression::DictComp(e, ref comp) =>
            format!("{{{} {}}}", format_dictitem(e), space_join(comp.iter().map(format_comp))),
        Expression::SetComp(e, ref comp) =>
            format!("{{{} {}}}", format_setitem(e), space_join(comp.iter().map(format_comp))),
        Expression::ListComp(e, ref comp) =>
            format!("[{} {}]", format_setitem(e), space_join(comp.iter().map(format_comp))),
        Expression::Generator(e, ref comp) =>
            format!("({} {})", format_setitem(e), space_join(comp.iter().map(format_comp))),

        Expression::Call(e, ref args) =>
            format!("{}({})", format_expr(e), format_args(args)),
        Expression::Subscript(e, ref sub) =>
            format!("{}[{}]", format_expr(e), comma_join(sub.iter().map(format_subscript))),
        Expression::Attribute(e, ref n) =>
            format!("{}.{}", format_expr(e), n),
        Expression::Uop(op, ref e) =>
            format!("{}{}", op, format_expr(e)),
        Expression::Bop(op, ref e1, ref e2) => {
            let f = |e:&_| match *e {
                Expression::Ellipsis | Expression::None | Expression::True |
                Expression::False | Expression::Int(_) |
                Expression::ImaginaryInt(_) | Expression::ImaginaryFloat(_) |
                Expression::Float(_) | Expression::String(_) | Expression::Bytes(_) |
                Expression::Name(_) | Expression::DictComp(_, _) | Expression::SetComp(_, _) |
                Expression::ListComp(_, _) | Expression::Generator(_, _) |
                Expression::DictLiteral(_) | Expression::SetLiteral(_) |
                Expression::ListLiteral(_) | Expression::TupleLiteral(_) =>
                    format!("{}", format_expr(e)),
                _ => format!("({})", format_expr(e)),
            };
            format!("{}{}{}", f(e1), op, f(e2))
        },
        Expression::MultiBop(ref first, ref rest) => {
            let mut s = String::new();
            s.push_str("(");
            s.push_str(&format_expr(first));
            s.push_str(")");
            for (op, e) in rest {
                s.push_str(" ");
                s.push_str(&op.to_string());
                s.push_str(" (");
                s.push_str(&format_expr(e));
                s.push_str(")");
            }
            s
        },
        Expression::Ternary(e1, e2, e3) =>
            format!("({}) if ({}) else ({})", format_expr(e1), format_expr(e2), format_expr(e3)),
        Expression::Star(ref e) =>
            format!("*{}", format_expr(e)),
        Expression::Yield(ref items) =>
            format!("yield {}", comma_join(items.iter().map(format_expr))),
        Expression::YieldFrom(ref iterable) => format!("yield from {}", format_expr(iterable)),
        Expression::Lambdef(ref params, ref body) =>
            format!("lambda {}: {}", format_untyped_params(params), format_expr(body))
    }
}

fn format_dotted_name(path: &[String]) -> String {
    let mut s = "".to_string();
    let mut first = true;
    for part in path {
        if first {
            first = false;
        }
        else {
            s.push_str(".");
        }
        s.push_str(part);
    }
    s
}

fn format_import(imp: &Import) -> String {
    let mut s = "".to_string();
    match *imp {
        Import::ImportFrom { leading_dots, ref path, ref names } => {
            s.push_str("from ");
            for _ in 0..leading_dots {
                s.push_str(".");
            }
            s.push_str(&format_dotted_name(path));
            s.push_str(" import ");
            s.push_str(&comma_join(names.iter().map(|(name, as_name)| {
                let mut s2 = String::new();
                s2.push_str(name);
                if let Some(as_name) = as_name {
                    s2.push_str(" as ");
                    s2.push_str(as_name);
                }
                s2
            })));
        },
        Import::Import { ref names } => {
            s.push_str("import ");
            s.push_str(&comma_join(names.iter().map(|(name, as_name)| {
                let mut s2 = String::new();
                s2.push_str(&format_dotted_name(name));
                if let Some(as_name) = as_name {
                    s2.push_str(" as ");
                    s2.push_str(as_name);
                }
                s2
            })));
        }
    }
    s
}
