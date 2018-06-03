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

pub fn format_module(stmts: &[Statement]) -> String {
    let mut s = "".to_string();
    for stmt in stmts {
        s.push_str(&format_statement(0, &stmt)[..])
    }
    s
}

fn format_statement(indent: usize, stmt: &Statement) -> String {
    let mut s = "".to_string();
    for _ in 0..indent {
        s.push_str(" ")
    }
    match *stmt {
        Statement::Pass => s.push_str("pass\n"),
        Statement::Del(ref names) => {
            s.push_str("del ");
            s.push_str(&comma_join(names));
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
        },
        _ => unimplemented!(),
    }
    s.push_str("\n");
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

fn format_expr(e: &Expression) -> String {
    match e {
        Expression::Ellipsis => "...".to_string(),
        Expression::None => "None".to_string(),
        Expression::True => "True".to_string(),
        Expression::False => "False".to_string(),
        Expression::Name(ref n) => n.to_string(),
        Expression::Int(ref n) => n.to_string(),
        Expression::String(ref s) => format!("{:?}", s), // FIXME: that's cheating
        Expression::DictLiteral(ref v) =>
            format!("[{}]", comma_join(v.iter().map(format_dictitem))),
        Expression::SetLiteral(ref v) =>
            format!("[{}]", comma_join(v.iter().map(format_setitem))),
        Expression::ListLiteral(ref v) =>
            format!("[{}]", comma_join(v.iter().map(format_setitem))),
        Expression::TupleLiteral(ref v) =>
            format!("[{}]", comma_join(v.iter().map(format_setitem))),
        Expression::Call(e, ref args) =>
            format!("{}({})", format_expr(e), format_args(args)),
        Expression::Subscript(e, ref sub) =>
            format!("{}[{}]", format_expr(e), comma_join(sub.iter().map(format_subscript))),
        Expression::Attribute(e, ref n) =>
            format!("{}.{}", format_expr(e), n),
        Expression::Uop(op, ref e) =>
            format!("{}{}", op, format_expr(e)),
        Expression::Bop(op, ref e1, ref e2) =>
            format!("({}){}({})", format_expr(e1), op, format_expr(e2)),
        Expression::Ternary(e1, e2, e3) =>
            format!("({}) if ({}) else ({})", format_expr(e1), format_expr(e2), format_expr(e3)),
        _ => unimplemented!(),
    }
}

fn format_dotted_name(path: &[String]) -> String {
    let mut s = "".to_string();
    let mut first = true;
    for part in path {
        if !first {
            s.push_str(".");
            first = false;
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
            for (name, as_name) in names {
                s.push_str(name);
                if let Some(as_name) = as_name {
                    s.push_str(" as ");
                    s.push_str(as_name);
                }
            }
        },
        Import::Import { ref names } => {
            s.push_str("import ");
            for (name, as_name) in names {
                s.push_str(&format_dotted_name(name));
                if let Some(as_name) = as_name {
                    s.push_str(" as ");
                    s.push_str(as_name);
                }
            }
        }
    }
    s
}
