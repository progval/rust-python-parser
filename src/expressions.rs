use std::marker::PhantomData;

use nom;
use nom::types::CompleteStr;
use nom::{IResult, Err, Context, ErrorKind};
use nom::Needed; // Required by escaped_transform, see https://github.com/Geal/nom/issues/780

use helpers::{Name, name};
use helpers::{AreNewlinesSpaces, NewlinesAreSpaces};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArgumentError {
    KeywordExpression,
    PositionalAfterKeyword,
    StarargsAfterKeyword,
}

impl ArgumentError {
    pub fn to_string(self) -> &'static str {
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
    Ellipsis,
    None,
    True,
    False,
    Name(Name),
    Int(i64),
    Complex { real: f64, imaginary: f64 },
    Float(f64),
    String(String),
    Bytes(Vec<u8>),
    Generator(Box<Expression>),
}

#[derive(Clone, Debug, PartialEq)]
enum RawArgument {
    Positional(Expression),
    Keyword(Expression, Expression),
    Starargs(Expression),
    Kwargs(Expression),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Argument<T> {
    Normal(T),
    Star(Expression),
}
#[derive(Clone, Debug, PartialEq)]
pub struct Arglist {
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
pub enum ComprehensionChunk {
    If { cond: Expression },
    For { async: bool, item: Vec<Expression>, iterator: Expression },
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
    Yield(Vec<Expression>),
    YieldFrom(Box<Expression>),
    Star(Box<Expression>),
    Generator(Box<Expression>, Vec<ComprehensionChunk>),
    CommaSeparated(Vec<Expression>),
}
pub(crate) struct ExpressionParser<ANS: AreNewlinesSpaces> {
    _phantom: PhantomData<ANS>,
}

impl<ANS: AreNewlinesSpaces> ExpressionParser<ANS> {

/*********************************************************************
 * Decorators
 *********************************************************************/

// test: or_test ['if' or_test 'else' test] | lambdef
named!(pub test<CompleteStr, Box<Expression>>,
  alt!(
    do_parse!(
      left: call!(Self::or_test) >>
      right: opt!(do_parse!(
        space_sep!() >>
        tag!("if") >>
        space_sep!() >>
        cond: call!(Self::or_test) >>
        space_sep!() >>
        tag!("else") >>
        space_sep!() >>
        right: call!(Self::test) >> (
          (cond, right)
        )
      )) >> (
        match right {
          None => left,
          Some((cond, right)) => Box::new(Expression::Ternary(left, cond, right)),
        }
      )
    )
  )
  // TODO
);

// test_nocond: or_test | lambdef_nocond
named!(test_nocond<CompleteStr, Box<Expression>>,
  alt!(
    call!(Self::or_test)
    // TODO
  )
);

// lambdef: 'lambda' [varargslist] ':' test
// TODO

// lambdef_nocond: 'lambda' [varargslist] ':' test_nocond
// TODO

} // End ExpressionParser

macro_rules! bop {
    ( $name:ident, $child:path, $tag:ident!($($args:tt)*) ) => {
    //( $name:ident, $child:tt, $tag1:ident!($($args1:tt)*) => $op1:tt, $( $tag:ident!($($args:tt)*) => $op:tt ),* ) => {
        named!($name<CompleteStr, Box<Expression>>,
          do_parse!(
            first: call!($child) >>
            r: fold_many0!(
              tuple!(
                delimited!(spaces!(), $tag!($($args)*), spaces!()),
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

impl<ANS: AreNewlinesSpaces> ExpressionParser<ANS> {

// or_test: and_test ('or' and_test)*
bop!(or_test, Self::and_test, alt!(
  tag!("or ") => { |_| Bop::Or }
));

// and_test: not_test ('and' not_test)*
bop!(and_test, Self::not_test, alt!(
  tag!("and ") => { |_| Bop::And }
));

// not_test: 'not' not_test | comparison
named!(not_test<CompleteStr, Box<Expression>>,
  alt!(
    preceded!(tag!("not "), call!(Self::comparison)) => { |e| Box::new(Expression::Uop(Uop::Not, e)) }
  | call!(Self::comparison)
  )
);

// comparison: expr (comp_op expr)*
// comp_op: '<'|'>'|'=='|'>='|'<='|'<>'|'!='|'in'|'not' 'in'|'is'|'is' 'not'
bop!(comparison, Self::expr, alt!(
  char!('<') => { |_| Bop::Lt }
| char!('>') => { |_| Bop::Gt }
| tag!("==") => { |_| Bop::Eq }
| tag!("<=") => { |_| Bop::Leq }
| tag!(">=") => { |_| Bop::Geq }
| tag!("!=") => { |_| Bop::Neq }
| tag!("in") => { |_| Bop::In }
| tuple!(tag!("not"), space_sep!(), tag!("in"), space_sep!()) => { |_| Bop::NotIn }
| tuple!(tag!("is"), space_sep!()) => { |_| Bop::Is }
| tuple!(tag!("is"), space_sep!(), tag!("not"), space_sep!()) => { |_| Bop::IsNot }
));

// star_expr: '*' expr
named!(star_expr<CompleteStr, Box<Expression>>,
 do_parse!(char!('*') >> spaces!() >> e: call!(Self::expr) >> (Box::new(Expression::Star(e))))
);

// expr: xor_expr ('|' xor_expr)*
bop!(expr, Self::xor_expr, alt!(
  char!('|') => { |_| Bop::BitOr }
));

// xor_expr: and_expr ('^' and_expr)*
bop!(xor_expr, Self::and_expr, alt!(
  char!('^') => { |_| Bop::BitXor }
));

// and_expr: shift_expr ('&' shift_expr)*
bop!(and_expr, Self::shift_expr, alt!(
  char!('&') => { |_| Bop::BitAnd }
));

// shift_expr: arith_expr (('<<'|'>>') arith_expr)*
bop!(shift_expr, Self::arith_expr, alt!(
  tag!("<<") => { |_| Bop::Lshift }
| tag!(">>") => { |_| Bop::Rshift }
));

// arith_expr: term (('+'|'-') term)*
bop!(arith_expr, Self::term, alt!(
  char!('+') => { |_| Bop::Add }
| char!('-') => { |_| Bop::Sub }
));

// term: factor (('*'|'@'|'/'|'%'|'//') factor)*
bop!(term, Self::factor, alt!(
  char!('*') => { |_| Bop::Mult }
| char!('@') => { |_| Bop::Matmult }
| char!('%') => { |_| Bop::Mod }
| tag!("//") => { |_| Bop::Floordiv }
| char!('/') => { |_| Bop::Div }
));

// factor: ('+'|'-'|'~') factor | power
named!(factor<CompleteStr, Box<Expression>>,
  alt!(
    do_parse!(spaces!() >> char!('+') >> spaces!() >> e: call!(Self::factor) >> (Box::new(Expression::Uop(Uop::Plus, e))))
  | do_parse!(spaces!() >> char!('-') >> spaces!() >> e: call!(Self::factor) >> (Box::new(Expression::Uop(Uop::Minus, e))))
  | do_parse!(spaces!() >> char!('~') >> spaces!() >> e: call!(Self::factor) >> (Box::new(Expression::Uop(Uop::Invert, e))))
  | call!(Self::power)
  )
);

// power: atom_expr ['**' factor]
named!(power<CompleteStr, Box<Expression>>,
  do_parse!(
    lhs: call!(Self::atom_expr) >>
    rhs: opt!(do_parse!(spaces!() >> tag!("**") >> spaces!() >> e: call!(Self::factor) >> (e))) >> (
      match rhs {
        Some(r) => Box::new(Expression::Bop(Bop::Power, lhs, r)),
        None => lhs,
      }
    )
  )
);

} // End ExpressionParser
enum Trailer { Call(Arglist), Subscript(Vec<Subscript>), Attribute(Name) }
impl<ANS: AreNewlinesSpaces> ExpressionParser<ANS> {

// atom_expr: [AWAIT] atom trailer*
// trailer: '(' [arglist] ')' | '[' subscriptlist ']' | '.' NAME
// subscriptlist: subscript (',' subscript)* [',']
named!(atom_expr<CompleteStr, Box<Expression>>,
  do_parse!(
    lhs: map!(call!(Self::atom), |a| Box::new(Expression::Atom(a))) >>
    trailers: fold_many0!(
      alt!(
        delimited!(char!('('), ws!(call!(ExpressionParser::<NewlinesAreSpaces>::arglist)), char!(')')) => { |args| Trailer::Call(args) }
      | delimited!(char!('['), ws!(separated_list!(char!(','), call!(ExpressionParser::<NewlinesAreSpaces>::subscript))), char!(']')) => { |i| Trailer::Subscript(i) }
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

// atom: ('(' [yield_expr|testlist_comp] ')' |
//       '[' [testlist_comp] ']' |
//       '{' [dictorsetmaker] '}' |
//       NAME | NUMBER | STRING+ | '...' | 'None' | 'True' | 'False')
named!(atom<CompleteStr, Atom>,
  alt!(
    tag!("...") => { |_| Atom::Ellipsis }
  | tag!("None") => { |_| Atom::None }
  | tag!("True") => { |_| Atom::True }
  | tag!("False") => { |_| Atom::False }
  | name => { |n| Atom::Name(n) }
  | separated_nonempty_list!(space_sep!(), delimited!(
      char!('"'),
      escaped_transform!(call!(nom::alpha), '\\', nom::anychar),
      char!('"')
    )) => { |strings: Vec<String>|
      Atom::String(strings.iter().fold("".to_string(), |mut acc, item| { acc.push_str(item); acc }))
    }
  | ws2!(delimited!(char!('('), ws!(alt!(call!(Self::yield_expr) | call!(Self::testlist_comp))), char!(')'))) => { |e| Atom::Generator(e) }
  // TODO
  )
);

// testlist_comp: (test|star_expr) ( comp_for | (',' (test|star_expr))* [','] )
named!(testlist_comp<CompleteStr, Box<Expression>>,
  do_parse!(
    first: alt!(call!(Self::test) | call!(Self::star_expr)) >>
    r: alt!(
      call!(Self::comp_for) => { |comp| Box::new(Expression::Generator(first, comp)) }
    | preceded!(char!(','), separated_list!(char!(','), alt!(call!(Self::test)|call!(Self::star_expr)))) => { |v: Vec<Box<Expression>>| {
        let mut v2 = vec![*first];
        v2.extend(v.into_iter().map(|e| *e));
        Box::new(Expression::CommaSeparated(v2))
      }}
    ) >> (
      r
    )
  )
);

// subscript: test | [test] ':' [test] [sliceop]
named!(subscript<CompleteStr, Subscript>,
  alt!(
    preceded!(char!(':'), call!(Self::subscript_trail, None))
  | do_parse!(
      first: call!(Self::test) >>
      r: opt!(preceded!(char!(':'), call!(Self::subscript_trail, Some(*first.clone())))) >> ( // FIXME: remove this clone
        r.unwrap_or(Subscript::Simple(*first))
      )
    )
  )
);
named_args!(subscript_trail(first: Option<Expression>) <CompleteStr, Subscript>,
  do_parse!(
    second: opt!(call!(Self::test)) >>
    third: opt!(preceded!(char!(':'), opt!(call!(Self::test)))) >> ({
      let second = second.map(|s| *s);
      match third {
        None => Subscript::Double(first, second),
        Some(None) => Subscript::Triple(first, second, None),
        Some(Some(t)) => Subscript::Triple(first, second, Some(*t)),
      }
    })
  )
);

// exprlist: (expr|star_expr) (',' (expr|star_expr))* [',']
named!(exprlist<CompleteStr, Vec<Expression>>,
  separated_nonempty_list!(ws2!(char!(',')), map!(alt!(call!(Self::expr)|call!(Self::star_expr)), |e| *e))
);

// testlist: test (',' test)* [',']
named!(pub testlist<CompleteStr, Vec<Expression>>,
  separated_nonempty_list!(ws2!(char!(',')), map!(call!(Self::test), |e| *e))
);
named!(pub possibly_empty_testlist<CompleteStr, Vec<Expression>>,
  separated_list!(ws2!(char!(',')), map!(call!(Self::test), |e| *e))
);

// dictorsetmaker: ( ((test ':' test | '**' expr)
//                    (comp_for | (',' (test ':' test | '**' expr))* [','])) |
//                   ((test | star_expr)
//                    (comp_for | (',' (test | star_expr))* [','])) )
// TODO

/*********************************************************************
 * Argument list
 *********************************************************************/

// arglist: argument (',' argument)*  [',']

// argument: ( test [comp_for] |
//             test '=' test |
//             '**' test |
//             '*' test )

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
            Some(RawArgument::Keyword(_, _arg)) => return fail(ArgumentError::KeywordExpression.into()),
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
        preceded!(tag!("**"), call!(Self::test)) => { |kwargs: Box<_>| RawArgument::Kwargs(*kwargs) }
      | preceded!(char!('*'), call!(Self::test)) => { |args: Box<_>| RawArgument::Starargs(*args) }
      | do_parse!(
          test1: call!(Self::test) >>
          next: opt!(alt!(
            preceded!(char!('='), call!(Self::test)) => { |test2: Box<_>| RawArgument::Keyword(*test1.clone(), *test2) } // FIXME: do not clone
          | call!(Self::comp_for) => { |v| RawArgument::Positional(Expression::Generator(test1.clone(), v)) } // FIXME: do not clone
          )) >> (
            match next {
                Some(e) => e,
                None => RawArgument::Positional(*test1)
            }
          )
        )
      )
    ) >>
    args2: call!(Self::build_arglist, args) >> (
      args2
    )
  )
);

/*********************************************************************
 * Iterator expressions
 *********************************************************************/

// comp_iter: comp_for | comp_if
named_args!(comp_iter(acc: Vec<ComprehensionChunk>) <CompleteStr, Vec<ComprehensionChunk>>,
  alt!(
    call!(Self::comp_for2, acc.clone()) // FIXME: do not clone
  | call!(Self::comp_if, acc)
  )
);

// comp_for: [ASYNC] 'for' exprlist 'in' or_test [comp_iter]
named!(comp_for<CompleteStr, Vec<ComprehensionChunk>>,
  call!(Self::comp_for2, Vec::new())
);
named_args!(comp_for2(acc: Vec<ComprehensionChunk>) <CompleteStr, Vec<ComprehensionChunk>>,
  do_parse!(
    async: map!(opt!(terminated!(tag!("async"), space_sep!())), |o| o.is_some()) >>
    tag!("for") >>
    space_sep!() >>
    item: call!(Self::exprlist) >>
    space_sep!() >>
    tag!("in") >>
    iterator: map!(call!(Self::or_test), |e| *e) >>
    space_sep!() >>
    r: call!(Self::comp_iter, { let mut acc = acc; acc.push(ComprehensionChunk::For { async, item, iterator }); acc }) >> (
      r
    )
  )
);

// comp_if: 'if' test_nocond [comp_iter]
named_args!(comp_if(acc: Vec<ComprehensionChunk>) <CompleteStr, Vec<ComprehensionChunk>>,
  do_parse!(
    tag!("if") >>
    space_sep!() >>
    cond: map!(call!(Self::test_nocond), |e| *e) >>
    space_sep!() >>
    r: call!(Self::comp_iter, { let mut acc = acc; acc.push(ComprehensionChunk::If { cond }); acc }) >> (
      r
    )
  )
);


// yield_expr: 'yield' [yield_arg]
// yield_arg: 'from' test | testlist
named!(pub yield_expr<CompleteStr, Box<Expression>>,
  preceded!(
    tuple!(tag!("yield"), space_sep!()),
    alt!(
      preceded!(tuple!(tag!("from"), space_sep!()), call!(Self::test)) => { |e| Box::new(Expression::YieldFrom(e)) }
    | call!(Self::testlist) => { |e| Box::new(Expression::Yield(e)) }
    )
  )
);

} // End ExpressionParser

/*********************************************************************
 * Unit tests
 *********************************************************************/

#[cfg(test)]
mod tests {
    use helpers::NewlinesAreNotSpaces;
    use super::*;
    use nom::types::CompleteStr as CS;

    #[test]
    fn test_atom() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;
        assert_eq!(atom(CS("foo ")), Ok((CS(" "), Atom::Name("foo".to_string()))));
        assert_eq!(atom(CS(r#""foo" "#)), Ok((CS(" "), Atom::String("foo".to_string()))));
        assert_eq!(atom(CS(r#""foo" "bar""#)), Ok((CS(""), Atom::String("foobar".to_string()))));
        assert_eq!(atom(CS(r#""fo\"o" "#)), Ok((CS(" "), Atom::String("fo\"o".to_string()))));
        assert_eq!(atom(CS(r#""fo"o" "#)), Ok((CS(r#"o" "#), Atom::String("fo".to_string()))));
    }

    #[test]
    fn test_ternary() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;
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
        let expr = ExpressionParser::<NewlinesAreNotSpaces>::expr;
        assert_eq!(expr(CS("foo & bar | baz ^ qux")), Ok((CS(""),
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

        assert_eq!(expr(CS("foo | bar & baz ^ qux")), Ok((CS(""),
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
        let shift_expr = ExpressionParser::<NewlinesAreNotSpaces>::shift_expr;
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
        let arith_expr = ExpressionParser::<NewlinesAreNotSpaces>::arith_expr;
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
        let term = ExpressionParser::<NewlinesAreNotSpaces>::term;
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
        let factor = ExpressionParser::<NewlinesAreNotSpaces>::factor;
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
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
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
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
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
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
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
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
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
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
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
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
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
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
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
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_eq!(atom_expr(CS("foo.bar")), Ok((CS(""),
            Box::new(Expression::Attribute(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                "bar".to_string(),
            ))
        )));
    }

    #[test]
    fn test_atom_expr() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
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

    #[test]
    fn test_call_newline() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        let ast =
            Box::new(Expression::Call(
                Box::new(Expression::Atom(Atom::Name("foo".to_string()))),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Atom(Atom::Name("bar".to_string()))
                        ),
                        Argument::Normal(
                            Expression::Bop(Bop::Add,
                                Box::new(Expression::Atom(Atom::Name("baz".to_string()))),
                                Box::new(Expression::Atom(Atom::Name("qux".to_string()))),
                            ),
                        ),
                    ],
                    keyword_args: vec![
                    ],
                },
            ));

        assert_eq!(atom_expr(CS("foo(bar, baz + qux)")), Ok((CS(""),
            ast.clone()
        )));

        assert_eq!(atom_expr(CS("foo(bar, baz +\nqux)")), Ok((CS(""),
            ast
        )));
    }
}
