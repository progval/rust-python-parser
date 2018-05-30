use nom;
use nom::types::CompleteStr;

use helpers::*;

#[derive(Clone, Debug, PartialEq)]
pub enum Atom {
    // TODO
    Name(Name),
    Int(i64),
    Complex { real: f64, imaginary: f64 },
    Float(f64),
    String(String),
    Bytes(Vec<u8>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Argument {
    Positional(Expression),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Subscript {
    Simple(Expression),
    Double(Option<Expression>, Option<Expression>),
    Triple(Option<Expression>, Option<Expression>, Option<Expression>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Uop {
    Plus,
    Minus,
    /// `~`
    Not,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Bop {
    Add,
    Sub,
    Mult,
    Matmult,
    Mod,
    Floordiv,
    Div,
    Power,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expression {
    Atom(Atom),
    Call(Box<Expression>, Vec<Argument>),
    Subscript(Box<Expression>, Vec<Subscript>),
    /// `foo.bar`
    Attribute(Box<Expression>, Name),
    /// Unary operator
    Uop(Uop, Box<Expression>),
    /// Binary operator
    Bop(Bop, Box<Expression>, Box<Expression>),
}

named!(test<CompleteStr, Expression>,
  // TODO
  map!(atom, |a| Expression::Atom(a))
);

named!(term<CompleteStr, Box<Expression>>,
  do_parse!(
    first: factor >>
    r: fold_many0!(
      tuple!(
        ws2!(alt!(
          char!('*') => { |_| Bop::Mult }
        | char!('@') => { |_| Bop::Matmult }
        | char!('%') => { |_| Bop::Mod }
        | tag!("//") => { |_| Bop::Floordiv }
        | char!('/') => { |_| Bop::Div }
        )),
        factor
      ),
      first,
      |acc, (op, f)| Box::new(Expression::Bop(op, acc, f))
    ) >> (
    r
    )
  )
);


named!(factor<CompleteStr, Box<Expression>>,
  alt!(
    preceded!(ws2!(char!('+')), factor) => { |e| Box::new(Expression::Uop(Uop::Plus, e)) }
  | preceded!(ws2!(char!('-')), factor) => { |e| Box::new(Expression::Uop(Uop::Minus, e)) }
  | preceded!(ws2!(char!('~')), factor) => { |e| Box::new(Expression::Uop(Uop::Not, e)) }
  | power
  )
);

named!(power<CompleteStr, Box<Expression>>,
  do_parse!(
    lhs: atom_expr >>
    rhs: opt!(preceded!(ws2!(tag!("**")), factor)) >> (
      match rhs {
        Some(r) => Box::new(Expression::Bop(Bop::Power, lhs, r)),
        None => lhs,
      }
    )
  )
);

enum Trailer { Call(Vec<Argument>), Subscript(Vec<Subscript>), Attribute(Name) }
named!(atom_expr<CompleteStr, Box<Expression>>,
  do_parse!(
    lhs: map!(atom, |a| Box::new(Expression::Atom(a))) >>
    trailers: fold_many0!(
      alt!(
        delimited!(char!('('), ws!(separated_list!(char!(','), argument)), char!(')')) => { |args| Trailer::Call(args) }
      | delimited!(char!('['), ws!(separated_list!(char!(','), subscript)), char!(']')) => { |i| Trailer::Subscript(i) }
      | preceded!(ws2!(char!('.')), name) => { |name| Trailer::Attribute(name) }
      ),
      lhs,
      |acc, item| Box::new(match item {
        Trailer::Call(args) => Expression::Call(acc, args),
        Trailer::Subscript(i) => Expression::Subscript(acc, i),
        Trailer::Attribute(name) => Expression::Attribute(acc, name),
      })
    ) >> (
      trailers
    )
  )
);

named!(argument<CompleteStr, Argument>,
  // TODO
  map!(test, |e| Argument::Positional(e))
);

named!(subscript<CompleteStr, Subscript>,
  alt!(
    preceded!(char!(':'), call!(subscript_trail, None))
  | do_parse!(
      first: test >> 
      r: opt!(preceded!(char!(':'), call!(subscript_trail, Some(first.clone())))) >> ( // FIXME: remove this clone
        r.unwrap_or(Subscript::Simple(first))
      )
    )
  )
);
named_args!(subscript_trail(first: Option<Expression>) <CompleteStr, Subscript>,
  do_parse!(
    second: opt!(test) >>
    third: opt!(preceded!(char!(':'), opt!(test))) >> ({
      match third {
        None => Subscript::Double(first, second),
        Some(t) => Subscript::Triple(first, second, t),
      }
    })
  )
);

use nom::Needed; // Required by escaped_transform, see https://github.com/Geal/nom/issues/780
named!(atom<CompleteStr, Atom>,
  alt!(
    name => { |n| Atom::Name(n) }
  | delimited!(
      char!('"'),
      escaped_transform!(call!(nom::alpha), '\\', nom::anychar),
      char!('"')
    ) => { |s| Atom::String(s) }
  )
  // TODO
);

#[cfg(test)]
mod tests {
    use super::*;
    use nom::types::CompleteStr as CS;

    #[test]
    fn test_atom() {
        assert_eq!(atom(CS("foo ")), Ok((CS(" "), Atom::Name("foo".to_string()))));
        assert_eq!(atom(CS(r#""foo" "#)), Ok((CS(" "), Atom::String("foo".to_string()))));
        assert_eq!(atom(CS(r#""fo\"o" "#)), Ok((CS(" "), Atom::String("fo\"o".to_string()))));
        assert_eq!(atom(CS(r#""fo"o" "#)), Ok((CS(r#"o" "#), Atom::String("fo".to_string()))));
    }

    #[test]
    fn test_term() {
        assert_eq!(term(CS("foo * bar")), Ok((CS(""),
            Box::new(Expression::Bop(Bop::Mult,
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Box::new(Expression::Atom(Atom::Name("bar".to_string()))),
            ))
        )));

        assert_eq!(term(CS("foo ** bar * baz")), Ok((CS(""),
            Box::new(Expression::Bop(Bop::Mult,
                Box::new(Expression::Bop(Bop::Power,
                    Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                    Box::new(Expression::Atom(Atom::Name("bar".to_string()))),
                )),
                Box::new(Expression::Atom(Atom::Name("baz".to_string()))),
            ))
        )));

        assert_eq!(term(CS("foo * bar ** baz")), Ok((CS(""),
            Box::new(Expression::Bop(Bop::Mult,
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Box::new(Expression::Bop(Bop::Power,
                    Box::new(Expression::Atom(Atom::Name("bar".to_string()))),
                    Box::new(Expression::Atom(Atom::Name("baz".to_string()))),
                )),
            ))
        )));
    }

    #[test]
    fn test_power() {
        assert_eq!(factor(CS("foo ** bar")), Ok((CS(""),
            Box::new(Expression::Bop(Bop::Power,
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Box::new(Expression::Atom(Atom::Name("bar".to_string()))),
            ))
        )));

        assert_eq!(factor(CS("foo ** + bar")), Ok((CS(""),
            Box::new(Expression::Bop(Bop::Power,
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Box::new(Expression::Uop(Uop::Plus,
                    Box::new(Expression::Atom(Atom::Name("bar".to_string()))),
                )),
            ))
        )));
    }

    #[test]
    fn test_call() {
        assert_eq!(atom_expr(CS("foo(bar)")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                vec![
                    Argument::Positional(
                        Expression::Atom(Atom::Name("bar".to_string()))
                    ),
                ],
            ))
        )));

        assert_eq!(atom_expr(CS("foo(bar, baz)")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                vec![
                    Argument::Positional(
                        Expression::Atom(Atom::Name("bar".to_string()))
                    ),
                    Argument::Positional(
                        Expression::Atom(Atom::Name("baz".to_string()))
                    ),
                ],
            ))
        )));
    }

    #[test]
    fn test_subscript_simple() {
        assert_eq!(atom_expr(CS("foo[bar]")), Ok((CS(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                vec![
                    Subscript::Simple(
                        Expression::Atom(Atom::Name("bar".to_string())),
                    )
                ],
            ))
        )));
    }

    #[test]
    fn test_subscript_double() {
        assert_eq!(atom_expr(CS("foo[bar:baz]")), Ok((CS(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                vec![
                    Subscript::Double(
                        Some(Expression::Atom(Atom::Name("bar".to_string()))),
                        Some(Expression::Atom(Atom::Name("baz".to_string()))),
                    )
                ],
            ))
        )));

        assert_eq!(atom_expr(CS("foo[bar:]")), Ok((CS(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                vec![
                    Subscript::Double(
                        Some(Expression::Atom(Atom::Name("bar".to_string()))),
                        None,
                    )
                ],
            ))
        )));

        assert_eq!(atom_expr(CS("foo[:baz]")), Ok((CS(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                vec![
                    Subscript::Double(
                        None,
                        Some(Expression::Atom(Atom::Name("baz".to_string()))),
                    )
                ],
            ))
        )));

        assert_eq!(atom_expr(CS("foo[:]")), Ok((CS(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                vec![
                    Subscript::Double(
                        None,
                        None,
                    )
                ],
            ))
        )));
    }

    #[test]
    fn test_subscript_triple() {
        assert_eq!(atom_expr(CS("foo[bar:baz:qux]")), Ok((CS(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                vec![
                    Subscript::Triple(
                        Some(Expression::Atom(Atom::Name("bar".to_string()))),
                        Some(Expression::Atom(Atom::Name("baz".to_string()))),
                        Some(Expression::Atom(Atom::Name("qux".to_string()))),
                    )
                ],
            ))
        )));

        assert_eq!(atom_expr(CS("foo[bar::qux]")), Ok((CS(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                vec![
                    Subscript::Triple(
                        Some(Expression::Atom(Atom::Name("bar".to_string()))),
                        None,
                        Some(Expression::Atom(Atom::Name("qux".to_string()))),
                    )
                ],
            ))
        )));

        assert_eq!(atom_expr(CS("foo[bar::]")), Ok((CS(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                vec![
                    Subscript::Triple(
                        Some(Expression::Atom(Atom::Name("bar".to_string()))),
                        None,
                        None,
                    )
                ],
            ))
        )));

        assert_eq!(atom_expr(CS("foo[:baz:qux]")), Ok((CS(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                vec![
                    Subscript::Triple(
                        None,
                        Some(Expression::Atom(Atom::Name("baz".to_string()))),
                        Some(Expression::Atom(Atom::Name("qux".to_string()))),
                    )
                ],
            ))
        )));

        assert_eq!(atom_expr(CS("foo[:baz:]")), Ok((CS(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                vec![
                    Subscript::Triple(
                        None,
                        Some(Expression::Atom(Atom::Name("baz".to_string()))),
                        None,
                    )
                ],
            ))
        )));

        assert_eq!(atom_expr(CS("foo[::]")), Ok((CS(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                vec![
                    Subscript::Triple(
                        None,
                        None,
                        None,
                    )
                ],
            ))
        )));
    }

    #[test]
    fn test_attribute() {
        assert_eq!(atom_expr(CS("foo.bar")), Ok((CS(""),
            Box::new(Expression::Attribute(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                "bar".to_string(),
            ))
        )));
    }

    #[test]
    fn test_atom_expr() {
        assert_eq!(atom_expr(CS("foo.bar[baz]")), Ok((CS(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Attribute(
                    Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                    "bar".to_string(),
                )),
                vec![
                    Subscript::Simple(
                        Expression::Atom(Atom::Name("baz".to_string())),
                    )
                ],
            ))
        )));
    }
}
