use nom;
use nom::types::CompleteStr;

use helpers::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArgumentError {
    KeywordExpression,
    PositionalAfterKeyword,
    StarargsAfterKeyword,
}

impl ArgumentError {
    fn to_string(self) -> &'static str {
        match self {
            ArgumentError::KeywordExpression => "Keyword cannot be an expression.",
            ArgumentError::PositionalAfterKeyword => "Positional argument after keyword argument or **kwargs.",
            ArgumentError::StarargsAfterKeyword => "*args after keyword argument or **kwargs.",
        }
    }
}

impl From<u32> for ArgumentError {
    fn from(i: u32) -> ArgumentError {
        match i {
            1 => ArgumentError::KeywordExpression,
            2 => ArgumentError::PositionalAfterKeyword,
            3 => ArgumentError::StarargsAfterKeyword,
            _ => panic!("Invalid error code.")
        }
    }
}

impl From<ArgumentError> for u32 {
    fn from(e: ArgumentError) -> u32 {
        match e {
            ArgumentError::KeywordExpression => 1,
            ArgumentError::PositionalAfterKeyword => 2,
            ArgumentError::StarargsAfterKeyword => 3,
        }
    }
}

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
enum RawArgument {
    Positional(Expression),
    Keyword(Expression, Expression),
    Starargs(Expression),
    Kwargs(Expression),
}

#[derive(Clone, Debug, PartialEq)]
enum Argument<T> {
    Normal(T),
    Star(Expression),
}
#[derive(Clone, Debug, PartialEq)]
struct Arglist {
    positional_args: Vec<Argument<Expression>>,
    keyword_args: Vec<Argument<(Name, Expression)>>,
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
    Invert,
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
    Lshift,
    Rshift,
    BitAnd,
    BitXor,
    BitOr,
    /// lower than
    Lt,
    /// greater than
    Gt,
    Eq,
    /// lower or equal
    Leq,
    /// greater or equal
    Geq,
    Neq,
    In,
    NotIn,
    Is,
    IsNot,
    And,
    Or,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expression {
    Atom(Atom),
    Call(Box<Expression>, Arglist),
    Subscript(Box<Expression>, Vec<Subscript>),
    /// `foo.bar`
    Attribute(Box<Expression>, Name),
    /// Unary operator
    Uop(Uop, Box<Expression>),
    /// Binary operator
    Bop(Bop, Box<Expression>, Box<Expression>),
    /// 1 if 2 else 3
    Ternary(Box<Expression>, Box<Expression>, Box<Expression>),
}

named!(test<CompleteStr, Box<Expression>>,
  alt!(
    do_parse!(
      left: or_test >>
      right: opt!(tuple!(delimited!(tag!(" if "), or_test, tag!(" else ")), test)) >> (
        match right {
          None => left,
          Some((cond, right)) => Box::new(Expression::Ternary(left, cond, right)),
        }
      )
    )
  )
  // TODO
);

macro_rules! bop {
    ( $name:ident, $child:tt, $tag:ident!($($args:tt)*) ) => {
    //( $name:ident, $child:tt, $tag1:ident!($($args1:tt)*) => $op1:tt, $( $tag:ident!($($args:tt)*) => $op:tt ),* ) => {
        named!($name<CompleteStr, Box<Expression>>,
          do_parse!(
            first: $child >>
            r: fold_many0!(
              tuple!(
                ws2!($tag!($($args)*)),
                /*ws2!(alt!(
                  $tag1($($args1)*) => { |_| $op1 }
                  $( | $tag($($args)*) => { |_| $op } )*
                )),*/
                $child
              ),
              first,
              |acc, (op, f)| Box::new(Expression::Bop(op, acc, f))
            ) >> (
            r
            )
          )
        );
    }
}

bop!(or_test, and_test, alt!(
  tag!("or") => { |_| Bop::Or }
));

bop!(and_test, not_test, alt!(
  tag!("and") => { |_| Bop::And }
));

named!(not_test<CompleteStr, Box<Expression>>,
  alt!(
    preceded!(ws2!(tag!("not")), comparison) => { |e| Box::new(Expression::Uop(Uop::Not, e)) }
  | comparison
  )
);

bop!(comparison, or_expr, alt!(
  char!('<') => { |_| Bop::Lt }
| char!('>') => { |_| Bop::Gt }
| tag!("==") => { |_| Bop::Eq }
| tag!("<=") => { |_| Bop::Leq }
| tag!(">=") => { |_| Bop::Geq }
| tag!("!=") => { |_| Bop::Neq }
| tag!("in") => { |_| Bop::In }
| ws2!(tuple!(tag!("not"), tag!("in"))) => { |_| Bop::NotIn }
| tag!("is") => { |_| Bop::Is }
| ws2!(tuple!(tag!("is"), tag!("not"))) => { |_| Bop::IsNot }
));

bop!(or_expr, xor_expr, alt!(
  char!('|') => { |_| Bop::BitOr }
));

bop!(xor_expr, and_expr, alt!(
  char!('^') => { |_| Bop::BitXor }
));

bop!(and_expr, shift_expr, alt!(
  char!('&') => { |_| Bop::BitAnd }
));

bop!(shift_expr, arith_expr, alt!(
  tag!("<<") => { |_| Bop::Lshift }
| tag!(">>") => { |_| Bop::Rshift }
));

bop!(arith_expr, term, alt!(
  char!('+') => { |_| Bop::Add }
| char!('-') => { |_| Bop::Sub }
));
/*
bop!(arith_expr, term,
  char!(('+')) => (Bop::Add),
  char!('-') => (Bop::Sub)
);*/

bop!(term, factor, alt!(
  char!('*') => { |_| Bop::Mult }
| char!('@') => { |_| Bop::Matmult }
| char!('%') => { |_| Bop::Mod }
| tag!("//") => { |_| Bop::Floordiv }
| char!('/') => { |_| Bop::Div }
));

named!(factor<CompleteStr, Box<Expression>>,
  alt!(
    preceded!(ws2!(char!('+')), factor) => { |e| Box::new(Expression::Uop(Uop::Plus, e)) }
  | preceded!(ws2!(char!('-')), factor) => { |e| Box::new(Expression::Uop(Uop::Minus, e)) }
  | preceded!(ws2!(char!('~')), factor) => { |e| Box::new(Expression::Uop(Uop::Invert, e)) }
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

enum Trailer { Call(Arglist), Subscript(Vec<Subscript>), Attribute(Name) }
named!(atom_expr<CompleteStr, Box<Expression>>,
  do_parse!(
    lhs: map!(atom, |a| Box::new(Expression::Atom(a))) >>
    trailers: fold_many0!(
      alt!(
        delimited!(char!('('), ws!(arglist), char!(')')) => { |args| Trailer::Call(args) }
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

use nom::{IResult, Err, Context, ErrorKind};
fn build_arglist(input: CompleteStr, args: Vec<RawArgument>) -> IResult<CompleteStr, Arglist> {
    let fail = |i| {
        Err(Err::Failure(Context::Code(input, ErrorKind::Custom(i))))
    };
    let mut iter = args.into_iter();
    let mut positional_args = Vec::<Argument<Expression>>::new();
    let mut keyword_args = Vec::<Argument<(Name, Expression)>>::new();
    let mut last_arg = iter.next();
    loop {
        match last_arg {
            Some(RawArgument::Positional(arg)) => positional_args.push(Argument::Normal(arg)),
            Some(RawArgument::Starargs(args)) => positional_args.push(Argument::Star(args)),
            _ => break,
        }
        last_arg = iter.next()
    }
    loop {
        match last_arg {
            Some(RawArgument::Keyword(Expression::Atom(Atom::Name(name)), arg)) => keyword_args.push(Argument::Normal((name, arg))),
            Some(RawArgument::Keyword(_, arg)) => return fail(ArgumentError::KeywordExpression.into()),
            Some(RawArgument::Kwargs(kwargs)) => keyword_args.push(Argument::Star(kwargs)),
            Some(RawArgument::Positional(_)) => return fail(ArgumentError::PositionalAfterKeyword.into()),
            Some(RawArgument::Starargs(_)) => return fail(ArgumentError::StarargsAfterKeyword.into()),
            None => break,
        }
        last_arg = iter.next()
    }

    Ok((input, Arglist { positional_args, keyword_args }))
}
named!(arglist<CompleteStr, Arglist>,
  do_parse!(
    args: separated_list!(ws!(char!(',')),
      alt!(
        tuple!(test, opt!(preceded!(char!('='), test))) => { |(test1, test2): (Box<_>, Option<Box<_>>)| {
          match test2 {
              None => RawArgument::Positional(*test1),
              Some(test2) => RawArgument::Keyword(*test1, *test2),
          }
        }}
      | preceded!(tag!("**"), test) => { |kwargs: Box<_>| RawArgument::Kwargs(*kwargs) }
      | preceded!(char!('*'), test) => { |args: Box<_>| RawArgument::Starargs(*args) }
      )
    ) >>
    args2: call!(build_arglist, args) >> (
      args2
    )
  )
);

named!(subscript<CompleteStr, Subscript>,
  alt!(
    preceded!(char!(':'), call!(subscript_trail, None))
  | do_parse!(
      first: test >> 
      r: opt!(preceded!(char!(':'), call!(subscript_trail, Some(*first.clone())))) >> ( // FIXME: remove this clone
        r.unwrap_or(Subscript::Simple(*first))
      )
    )
  )
);
named_args!(subscript_trail(first: Option<Expression>) <CompleteStr, Subscript>,
  do_parse!(
    second: opt!(test) >>
    third: opt!(preceded!(char!(':'), opt!(test))) >> ({
      let second = second.map(|s| *s);
      match third {
        None => Subscript::Double(first, second),
        Some(None) => Subscript::Triple(first, second, None),
        Some(Some(t)) => Subscript::Triple(first, second, Some(*t)),
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
    fn test_ternary() {
        assert_eq!(test(CS("foo if bar else baz")), Ok((CS(""),
            Box::new(Expression::Ternary(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Box::new(Expression::Atom(Atom::Name("bar".to_string()))),
                Box::new(Expression::Atom(Atom::Name("baz".to_string()))),
            ))
        )));
    }

    #[test]
    fn test_bool_ops() {
        assert_eq!(or_expr(CS("foo & bar | baz ^ qux")), Ok((CS(""),
            Box::new(Expression::Bop(Bop::BitOr,
                Box::new(Expression::Bop(Bop::BitAnd,
                    Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                    Box::new(Expression::Atom(Atom::Name("bar".to_string()))),
                )),
                Box::new(Expression::Bop(Bop::BitXor,
                    Box::new(Expression::Atom(Atom::Name("baz".to_string()))),
                    Box::new(Expression::Atom(Atom::Name("qux".to_string()))),
                )),
            ))
        )));

        assert_eq!(or_expr(CS("foo | bar & baz ^ qux")), Ok((CS(""),
            Box::new(Expression::Bop(Bop::BitOr,
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Box::new(Expression::Bop(Bop::BitXor,
                    Box::new(Expression::Bop(Bop::BitAnd,
                        Box::new(Expression::Atom(Atom::Name("bar".to_string()))),
                        Box::new(Expression::Atom(Atom::Name("baz".to_string()))),
                    )),
                    Box::new(Expression::Atom(Atom::Name("qux".to_string()))),
                )),
            ))
        )));
    }

    #[test]
    fn test_shift_expr() {
        assert_eq!(shift_expr(CS("foo << bar")), Ok((CS(""),
            Box::new(Expression::Bop(Bop::Lshift,
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Box::new(Expression::Atom(Atom::Name("bar".to_string()))),
            ))
        )));

        assert_eq!(shift_expr(CS("foo >> bar")), Ok((CS(""),
            Box::new(Expression::Bop(Bop::Rshift,
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Box::new(Expression::Atom(Atom::Name("bar".to_string()))),
            ))
        )));
    }

    #[test]
    fn test_arith_expr() {
        assert_eq!(arith_expr(CS("foo + bar")), Ok((CS(""),
            Box::new(Expression::Bop(Bop::Add,
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Box::new(Expression::Atom(Atom::Name("bar".to_string()))),
            ))
        )));

        assert_eq!(arith_expr(CS("foo * bar + baz")), Ok((CS(""),
            Box::new(Expression::Bop(Bop::Add,
                Box::new(Expression::Bop(Bop::Mult,
                    Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                    Box::new(Expression::Atom(Atom::Name("bar".to_string()))),
                )),
                Box::new(Expression::Atom(Atom::Name("baz".to_string()))),
            ))
        )));

        assert_eq!(arith_expr(CS("foo + bar * baz")), Ok((CS(""),
            Box::new(Expression::Bop(Bop::Add,
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Box::new(Expression::Bop(Bop::Mult,
                    Box::new(Expression::Atom(Atom::Name("bar".to_string()))),
                    Box::new(Expression::Atom(Atom::Name("baz".to_string()))),
                )),
            ))
        )));
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
    fn test_call_noarg() {
        assert_eq!(atom_expr(CS("foo()")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Arglist {
                    positional_args: vec![
                    ],
                    keyword_args: vec![
                    ],
                },
            ))
        )));
    }

    #[test]
    fn test_call_positional() {
        assert_eq!(atom_expr(CS("foo(bar)")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Atom(Atom::Name("bar".to_string()))
                        ),
                    ],
                    keyword_args: vec![
                    ],
                },
            ))
        )));

        assert_eq!(atom_expr(CS("foo(bar, baz)")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Atom(Atom::Name("bar".to_string()))
                        ),
                        Argument::Normal(
                            Expression::Atom(Atom::Name("baz".to_string()))
                        ),
                    ],
                    keyword_args: vec![
                    ],
                },
            ))
        )));

        assert_eq!(atom_expr(CS("foo(bar, baz, *qux)")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Atom(Atom::Name("bar".to_string()))
                        ),
                        Argument::Normal(
                            Expression::Atom(Atom::Name("baz".to_string()))
                        ),
                        Argument::Star(
                            Expression::Atom(Atom::Name("qux".to_string()))
                        ),
                    ],
                    keyword_args: vec![
                    ],
                },
            ))
        )));

        assert_eq!(atom_expr(CS("foo(bar, *baz, qux)")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Atom(Atom::Name("bar".to_string()))
                        ),
                        Argument::Star(
                            Expression::Atom(Atom::Name("baz".to_string()))
                        ),
                        Argument::Normal(
                            Expression::Atom(Atom::Name("qux".to_string()))
                        ),
                    ],
                    keyword_args: vec![
                    ],
                },
            ))
        )));

        assert_eq!(atom_expr(CS("foo(bar, *baz, *qux)")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Atom(Atom::Name("bar".to_string()))
                        ),
                        Argument::Star(
                            Expression::Atom(Atom::Name("baz".to_string()))
                        ),
                        Argument::Star(
                            Expression::Atom(Atom::Name("qux".to_string()))
                        ),
                    ],
                    keyword_args: vec![
                    ],
                },
            ))
        )));
    }

    #[test]
    fn test_call_keyword() {
        assert_eq!(atom_expr(CS("foo(bar1=bar2)")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Arglist {
                    positional_args: vec![
                    ],
                    keyword_args: vec![
                        Argument::Normal(
                            ("bar1".to_string(), Expression::Atom(Atom::Name("bar2".to_string()))),
                        ),
                    ],
                },
            ))
        )));

        assert_eq!(atom_expr(CS("foo(bar1=bar2, baz1=baz2)")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Arglist {
                    positional_args: vec![
                    ],
                    keyword_args: vec![
                        Argument::Normal(
                            ("bar1".to_string(), Expression::Atom(Atom::Name("bar2".to_string()))),
                        ),
                        Argument::Normal(
                            ("baz1".to_string(), Expression::Atom(Atom::Name("baz2".to_string()))),
                        ),
                    ],
                },
            ))
        )));

        assert_eq!(atom_expr(CS("foo(bar1=bar2, baz1=baz2, qux1=qux2)")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Arglist {
                    positional_args: vec![
                    ],
                    keyword_args: vec![
                        Argument::Normal(
                            ("bar1".to_string(), Expression::Atom(Atom::Name("bar2".to_string()))),
                        ),
                        Argument::Normal(
                            ("baz1".to_string(), Expression::Atom(Atom::Name("baz2".to_string()))),
                        ),
                        Argument::Normal(
                            ("qux1".to_string(), Expression::Atom(Atom::Name("qux2".to_string()))),
                        ),
                    ],
                },
            ))
        )));

        assert_eq!(atom_expr(CS("foo(bar1=bar2, baz1=baz2, **qux)")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Arglist {
                    positional_args: vec![
                    ],
                    keyword_args: vec![
                        Argument::Normal(
                            ("bar1".to_string(), Expression::Atom(Atom::Name("bar2".to_string()))),
                        ),
                        Argument::Normal(
                            ("baz1".to_string(), Expression::Atom(Atom::Name("baz2".to_string()))),
                        ),
                        Argument::Star(
                            Expression::Atom(Atom::Name("qux".to_string())),
                        ),
                    ],
                },
            ))
        )));

        assert_eq!(atom_expr(CS("foo(bar1=bar2, **baz, **qux)")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Arglist {
                    positional_args: vec![
                    ],
                    keyword_args: vec![
                        Argument::Normal(
                            ("bar1".to_string(), Expression::Atom(Atom::Name("bar2".to_string()))),
                        ),
                        Argument::Star(
                            Expression::Atom(Atom::Name("baz".to_string())),
                        ),
                        Argument::Star(
                            Expression::Atom(Atom::Name("qux".to_string())),
                        ),
                    ],
                },
            ))
        )));

        assert_eq!(atom_expr(CS("foo(bar1=bar2, **baz, qux1=qux2)")), Ok((CS(""),
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Arglist {
                    positional_args: vec![
                    ],
                    keyword_args: vec![
                        Argument::Normal(
                            ("bar1".to_string(), Expression::Atom(Atom::Name("bar2".to_string()))),
                        ),
                        Argument::Star(
                            Expression::Atom(Atom::Name("baz".to_string())),
                        ),
                        Argument::Normal(
                            ("qux1".to_string(), Expression::Atom(Atom::Name("qux2".to_string()))),
                        ),
                    ],
                },
            ))
        )));
    }

    #[test]
    fn call_badargs() {
        assert_eq!(atom_expr(CS("foo(bar()=baz)")),
            Err(nom::Err::Failure(Context::Code(CS(")"),
                ErrorKind::Custom(ArgumentError::KeywordExpression.into())
            )))
        );

        assert_eq!(atom_expr(CS("foo(**baz, qux)")),
            Err(nom::Err::Failure(Context::Code(CS(")"),
                ErrorKind::Custom(ArgumentError::PositionalAfterKeyword.into())
            )))
        );

        assert_eq!(atom_expr(CS("foo(**baz, *qux)")),
            Err(nom::Err::Failure(Context::Code(CS(")"),
                ErrorKind::Custom(ArgumentError::StarargsAfterKeyword.into())
            )))
        );

        assert_eq!(atom_expr(CS("foo(bar1=bar2, qux)")),
            Err(nom::Err::Failure(Context::Code(CS(")"),
                ErrorKind::Custom(ArgumentError::PositionalAfterKeyword.into())
            )))
        );

        assert_eq!(atom_expr(CS("foo(bar1=bar2, *qux)")),
            Err(nom::Err::Failure(Context::Code(CS(")"),
                ErrorKind::Custom(ArgumentError::StarargsAfterKeyword.into())
            )))
        );
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
