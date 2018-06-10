use std::marker::PhantomData;

use nom::{IResult, Err, Context, ErrorKind};
//use unicode_names;

use helpers;
use helpers::{StrSpan, name};
use helpers::{AreNewlinesSpaces, NewlinesAreSpaces};
use functions::varargslist;
use bytes::bytes;
use strings::string;
use numbers::number;
use ast::*;

#[derive(Clone, Debug, PartialEq)]
enum RawArgument {
    Positional(Expression),
    Keyword(Expression, Expression),
    Starargs(Expression),
    Kwargs(Expression),
}

#[derive(Clone, Debug, PartialEq)]
enum TestlistCompReturn {
    Comp(Box<SetItem>, Vec<ComprehensionChunk>), // comprehension
    Lit(Vec<SetItem>), // list of litterals (length >= 1)
    Single(SetItem), // a single litteral: either from `[foo]` (list) or `(foo)` (atom, NOT tuple)
}

pub(crate) struct ExpressionParser<ANS: AreNewlinesSpaces> {
    _phantom: PhantomData<ANS>,
}

impl<ANS: AreNewlinesSpaces> ExpressionParser<ANS> {

/*********************************************************************
 * Decorators
 *********************************************************************/

// test: or_test ['if' or_test 'else' test] | lambdef
named!(pub test<StrSpan, Box<Expression>>,
  alt!(
    call!(Self::lambdef)
  | do_parse!(
      left: call!(Self::or_test) >>
      right: opt!(do_parse!(
        spaces!() >>
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
);

// test_nocond: or_test | lambdef_nocond
named!(test_nocond<StrSpan, Box<Expression>>,
  alt!(
    call!(Self::lambdef_nocond)
  | call!(Self::or_test)
  )
);

// lambdef: 'lambda' [varargslist] ':' test
named!(lambdef<StrSpan, Box<Expression>>,
  do_parse!(
    tag!("lambda") >>
    args: opt!(preceded!(space_sep!(), varargslist)) >>
    spaces!() >>
    char!(':') >>
    spaces!() >>
    code: call!(Self::test) >> (
      Box::new(Expression::Lambdef(args.unwrap_or_default(), code))
    )
  )
);

// lambdef_nocond: 'lambda' [varargslist] ':' test_nocond
named!(lambdef_nocond<StrSpan, Box<Expression>>,
  do_parse!(
    tag!("lambda") >>
    space_sep!() >>
    args: opt!(varargslist) >>
    char!(':') >>
    code: call!(Self::test_nocond) >> (
      Box::new(Expression::Lambdef(args.unwrap_or_default(), code))
    )
  )
);

} // End ExpressionParser

macro_rules! bop {
    ( $name:ident, $child:path, $tag:ident!($($args:tt)*) ) => {
        named!(pub $name<StrSpan, Box<Expression>>,
          do_parse!(
            first: call!($child) >>
            r: fold_many0!(
              tuple!(
                delimited!(spaces!(), $tag!($($args)*), spaces!()),
                $child
              ),
              (first, Vec::new()),
              |(first, mut acc):(_,Vec<_>), (op, f):(_,Box<_>)| { acc.push((op, *f)); (first, acc) }
            ) >> ({
              let (first, rest) = r;
              match rest.len() {
                  0 => first,
                  1 => {
                      let (op, ref rhs) = rest[0];
                      Box::new(Expression::Bop(op, first, Box::new(rhs.clone())))
                  }
                  _ => Box::new(Expression::MultiBop(first, rest))
              }
            })
          )
        );
    }
}

impl<ANS: AreNewlinesSpaces> ExpressionParser<ANS> {

// or_test: and_test ('or' and_test)*
bop!(or_test, Self::and_test, alt!(
  tuple!(tag!("or"), space_sep!()) => { |_| Bop::Or }
));

// and_test: not_test ('and' not_test)*
bop!(and_test, Self::not_test, alt!(
  tuple!(tag!("and"), space_sep!()) => { |_| Bop::And }
));

// not_test: 'not' not_test | comparison
named!(not_test<StrSpan, Box<Expression>>,
  alt!(
    preceded!(tuple!(tag!("not"), space_sep!()), call!(Self::comparison)) => { |e| Box::new(Expression::Uop(Uop::Not, e)) }
  | call!(Self::comparison)
  )
);

// comparison: expr (comp_op expr)*
// comp_op: '<'|'>'|'=='|'>='|'<='|'<>'|'!='|'in'|'not' 'in'|'is'|'is' 'not'
bop!(comparison, Self::expr, alt!(
  tag!("==") => { |_| Bop::Eq }
| tag!("<=") => { |_| Bop::Leq }
| tag!(">=") => { |_| Bop::Geq }
| char!('<') => { |_| Bop::Lt }
| char!('>') => { |_| Bop::Gt }
| tag!("!=") => { |_| Bop::Neq }
| tag!("in") => { |_| Bop::In }
| tuple!(tag!("not"), space_sep!(), tag!("in"), space_sep!()) => { |_| Bop::NotIn }
| tuple!(tag!("is"), space_sep!(), tag!("not"), space_sep!()) => { |_| Bop::IsNot }
| tuple!(tag!("is"), space_sep!()) => { |_| Bop::Is }
));

// star_expr: '*' expr
named!(pub star_expr<StrSpan, Box<Expression>>,
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
named!(factor<StrSpan, Box<Expression>>,
  alt!(
    do_parse!(spaces!() >> char!('+') >> spaces!() >> e: call!(Self::factor) >> (Box::new(Expression::Uop(Uop::Plus, e))))
  | do_parse!(spaces!() >> char!('-') >> spaces!() >> e: call!(Self::factor) >> (Box::new(Expression::Uop(Uop::Minus, e))))
  | do_parse!(spaces!() >> char!('~') >> spaces!() >> e: call!(Self::factor) >> (Box::new(Expression::Uop(Uop::Invert, e))))
  | call!(Self::power)
  )
);

// power: atom_expr ['**' factor]
named!(power<StrSpan, Box<Expression>>,
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
named!(atom_expr<StrSpan, Box<Expression>>,
  do_parse!(
    lhs: call!(Self::atom) >>
    trailers: fold_many0!(
      alt!(
        delimited!(char!('('), ws4!(call!(ExpressionParser::<NewlinesAreSpaces>::arglist)), char!(')')) => { |args| Trailer::Call(args) }
      | delimited!(char!('['), ws4!(separated_list!(char!(','), call!(ExpressionParser::<NewlinesAreSpaces>::subscript))), char!(']')) => { |i| Trailer::Subscript(i) }
      | preceded!(ws3!(char!('.')), name) => { |name| Trailer::Attribute(name) }
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
named!(atom<StrSpan, Box<Expression>>,
  map!(alt!(
    tag!("...") => { |_| Expression::Ellipsis }
  | tag!("None") => { |_| Expression::None }
  | tag!("True") => { |_| Expression::True }
  | tag!("False") => { |_| Expression::False }
  | separated_nonempty_list!(spaces!(), string) => { |s| Expression::String(s) }
  | separated_nonempty_list!(spaces!(), bytes) => { |v| {
      let mut v2 = Vec::new();
      for b in v { v2.extend(b) }
      Expression::Bytes(v2)
    }}
  | number
  | name => { |n| Expression::Name(n) }
  | ws3!(tuple!(char!('['), ws4!(opt!(char!(' '))), char!(']'))) => { |_| Expression::ListLiteral(vec![]) }
  | ws3!(tuple!(char!('{'), ws4!(opt!(char!(' '))), char!('}'))) => { |_| Expression::DictLiteral(vec![]) }
  | ws3!(tuple!(char!('('), ws4!(opt!(char!(' '))), char!(')'))) => { |_| Expression::TupleLiteral(vec![]) }
  | ws3!(delimited!(char!('{'), ws4!(map!(
      call!(ExpressionParser::<NewlinesAreSpaces>::dictorsetmaker), |e:Box<_>| *e
    )), char!('}')))
  | map_opt!(ws3!(delimited!(char!('('), ws4!(
      call!(ExpressionParser::<NewlinesAreSpaces>::testlist_comp)
    ), char!(')'))),  |ret| {
      match ret {
          // Case 1: (foo for ...) or (*foo for ...)
          TestlistCompReturn::Comp(e, comp) => Some(Expression::Generator(e, comp)),
          // Case 2: (foo,) or (foo, bar ...)
          TestlistCompReturn::Lit(v) => Some(Expression::TupleLiteral(v)),
          // Case 3: (foo)
          TestlistCompReturn::Single(SetItem::Unique(e)) => Some(e),
          // Forbidden case: (*foo)
          TestlistCompReturn::Single(SetItem::Star(_)) => None,
      }
    })
  | ws3!(delimited!(char!('('), ws4!(
      call!(ExpressionParser::<NewlinesAreSpaces>::yield_expr)
    ), char!(')')))
  | ws3!(delimited!(char!('['), ws4!(
      call!(ExpressionParser::<NewlinesAreSpaces>::testlist_comp)
    ), char!(']'))) => { |ret| {
      match ret {
          TestlistCompReturn::Comp(e, comp) => Expression::ListComp(e, comp),
          TestlistCompReturn::Lit(v) => Expression::ListLiteral(v),
          TestlistCompReturn::Single(e) => Expression::ListLiteral(vec![e]),
      }}
    }
  ), |e| Box::new(e))
);

// testlist_comp: (test|star_expr) ( comp_for | (',' (test|star_expr))* [','] )
named!(testlist_comp<StrSpan, TestlistCompReturn>,
  do_parse!(
    first: ws3!(alt!(
        call!(Self::test) => { |e: Box<_>| SetItem::Unique(*e) }
      | call!(Self::star_expr) => { |e: Box<_>| SetItem::Star(*e) }
      )) >>
    r: alt!(
      call!(Self::comp_for) => { |comp| TestlistCompReturn::Comp(Box::new(first), comp) }
    | opt!(delimited!(
        ws3!(char!(',')),
        separated_list!(ws3!(char!(',')),
          alt!(
            call!(Self::test) => { |e: Box<_>| SetItem::Unique(*e) }
          | call!(Self::star_expr) => { |e: Box<_>| SetItem::Star(*e) }
          )
        ),
        ws3!(opt!(char!(',')))
      )) => { |v: Option<Vec<SetItem>>| {
        match v {
            Some(v) => {
                let mut v = v;
                v.insert(0, first);
                TestlistCompReturn::Lit(v)
            },
            None => TestlistCompReturn::Single(first),
        }
      }}
    ) >> (
      r
    )
  )
);

// subscript: test | [test] ':' [test] [sliceop]
named!(subscript<StrSpan, Subscript>,
  ws4!(alt!(
    preceded!(char!(':'), call!(Self::subscript_trail, None))
  | do_parse!(
      first: call!(Self::test) >>
      r: opt!(ws4!(preceded!(char!(':'), call!(Self::subscript_trail, Some(*first.clone()))))) >> ( // FIXME: remove this clone
        r.unwrap_or(Subscript::Simple(*first))
      )
    )
  ))
);
named_args!(subscript_trail(first: Option<Expression>) <StrSpan, Subscript>,
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
named!(pub exprlist<StrSpan, Vec<Expression>>,
  separated_nonempty_list!(ws3!(char!(',')), map!(alt!(call!(Self::expr)|call!(Self::star_expr)), |e| *e))
);

// testlist: test (',' test)* [',']
named!(pub testlist<StrSpan, Vec<Expression>>,
  separated_nonempty_list!(ws3!(char!(',')), map!(call!(Self::test), |e| *e))
);
named!(pub possibly_empty_testlist<StrSpan, Vec<Expression>>,
  separated_list!(ws3!(char!(',')), map!(call!(Self::test), |e| *e))
);

} // end ExpressionParser

/*********************************************************************
 * Dictionary and set literals and comprehension
 *********************************************************************/

impl ExpressionParser<NewlinesAreSpaces> {

// dictorsetmaker: ( ((test ':' test | '**' expr)
//                    (comp_for | (',' (test ':' test | '**' expr))* [','])) |
//                   ((test | star_expr)
//                    (comp_for | (',' (test | star_expr))* [','])) )
named!(dictorsetmaker<StrSpan, Box<Expression>>,
  ws4!(alt!(
    do_parse!(
      tag!("**") >>
      e: map!(call!(Self::expr), |e: Box<_>| DictItem::Star(*e)) >>
      r: call!(Self::dictmaker, e) >>
      (r)
    )
  | do_parse!(
      tag!("*") >>
      e: map!(call!(Self::expr), |e: Box<_>| SetItem::Star(*e)) >>
      r: call!(Self::setmaker, e) >>
      (r)
    )
  | do_parse!(
      key: call!(Self::test) >>
      r: alt!(
        do_parse!(
          char!(':') >>
          item: map!(call!(Self::test), |value: Box<_>| DictItem::Unique(*key.clone(), *value)) >> // FIXME: do not clone
          r: call!(Self::dictmaker, item) >>
          (r)
        )
      | call!(Self::setmaker, SetItem::Unique(*key))
      ) >>
      (r)
    )
  ))
);

named_args!(dictmaker(item1: DictItem) <StrSpan, Box<Expression>>,
  map!(
    opt!(alt!(
      ws4!(delimited!(char!(','), separated_list!(char!(','), call!(Self::dictitem)), opt!(ws4!(char!(','))))) => { |v: Vec<_>| {
        let mut v = v;
        v.insert(0, item1.clone()); // FIXME: do not clone
        Box::new(Expression::DictLiteral(v))
      }}
    | preceded!(peek!(tuple!(tag!("for"), call!(helpers::space_sep))), call!(Self::comp_for)) => { |comp| {
        Box::new(Expression::DictComp(Box::new(item1.clone()), comp)) // FIXME: do not clone
      }}
    )),
    |rest| {
      match rest {
          Some(r) => r,
          None => Box::new(Expression::DictLiteral(vec![item1])),
      }
    }
  )
);

named_args!(setmaker(item1: SetItem) <StrSpan, Box<Expression>>,
  do_parse!(
    rest:opt!(alt!(
      ws4!(delimited!(char!(','), separated_list!(char!(','), call!(Self::setitem)), opt!(ws4!(char!(','))))) => { |v: Vec<_>| {
        let mut v = v;
        v.insert(0, item1.clone()); // FIXME: do not clone
        Box::new(Expression::SetLiteral(v))
      }}
    | call!(Self::comp_for) => { |comp| {
        Box::new(Expression::SetComp(Box::new(item1.clone()), comp)) // FIXME: do not clone
      }}
    )) >> (
      match rest {
          Some(r) => r,
          None => Box::new(Expression::SetLiteral(vec![item1])),
      }
    )
  )
);

named!(dictitem<StrSpan, DictItem>,
  ws4!(alt!(
    preceded!(tag!("**"), call!(Self::expr)) => { |e:Box<_>| DictItem::Star(*e) }
  | tuple!(call!(Self::test), char!(':'), call!(Self::test)) => { |(e1,_,e2): (Box<_>,_,Box<_>)| DictItem::Unique(*e1,*e2) }
  ))
);

named!(setitem<StrSpan, SetItem>,
  ws4!(alt!(
    preceded!(tag!("*"), call!(Self::expr)) => { |e:Box<_>| SetItem::Star(*e) }
  |call!(Self::test) => { |e:Box<_>| SetItem::Unique(*e) }
  ))
);

} // end ExpressionParser


/*********************************************************************
 * Argument list
 *********************************************************************/

impl<ANS: AreNewlinesSpaces> ExpressionParser<ANS> {

// arglist: argument (',' argument)*  [',']

// argument: ( test [comp_for] |
//             test '=' test |
//             '**' test |
//             '*' test )

fn build_arglist(input: StrSpan, args: Vec<RawArgument>) -> IResult<StrSpan, Arglist> {
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
            Some(RawArgument::Keyword(Expression::Name(name), arg)) => keyword_args.push(Argument::Normal((name, arg))),
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
named!(pub arglist<StrSpan, Arglist>,
  do_parse!(
    args: separated_list!(ws4!(char!(',')),
      alt!(
        preceded!(tag!("**"), call!(Self::test)) => { |kwargs: Box<_>| RawArgument::Kwargs(*kwargs) }
      | preceded!(char!('*'), call!(Self::test)) => { |args: Box<_>| RawArgument::Starargs(*args) }
      | do_parse!(
          test1: call!(Self::test) >>
          next: opt!(alt!(
            preceded!(char!('='), call!(Self::test)) => { |test2: Box<_>| RawArgument::Keyword(*test1.clone(), *test2) } // FIXME: do not clone
          | call!(Self::comp_for) => { |v| RawArgument::Positional(Expression::Generator(Box::new(SetItem::Unique(*test1.clone())), v)) } // FIXME: do not clone
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
named_args!(comp_iter(acc: Vec<ComprehensionChunk>) <StrSpan, Vec<ComprehensionChunk>>,
  alt!(
    call!(Self::comp_for2, acc.clone()) // FIXME: do not clone
  | call!(Self::comp_if, acc)
  )
);

named_args!(opt_comp_iter(acc: Vec<ComprehensionChunk>) <StrSpan, Vec<ComprehensionChunk>>,
  map!(opt!(call!(Self::comp_iter, acc.clone())), |r| r.unwrap_or(acc)) // FIXME: do not clone
);

// comp_for: [ASYNC] 'for' exprlist 'in' or_test [comp_iter]
named!(comp_for<StrSpan, Vec<ComprehensionChunk>>,
  call!(Self::comp_for2, Vec::new())
);
named_args!(comp_for2(acc: Vec<ComprehensionChunk>) <StrSpan, Vec<ComprehensionChunk>>,
  do_parse!(
    async: map!(opt!(terminated!(tag!("async"), space_sep!())), |o| o.is_some()) >>
    tag!("for") >>
    space_sep!() >>
    item: call!(Self::exprlist) >>
    space_sep!() >>
    tag!("in") >>
    space_sep!() >>
    iterator: map!(call!(Self::or_test), |e| *e) >>
    spaces!() >>
    r: call!(Self::opt_comp_iter, { let mut acc = acc; acc.push(ComprehensionChunk::For { async, item, iterator }); acc }) >> (
      r
    )
  )
);

// comp_if: 'if' test_nocond [comp_iter]
named_args!(comp_if(acc: Vec<ComprehensionChunk>) <StrSpan, Vec<ComprehensionChunk>>,
  do_parse!(
    tag!("if") >>
    space_sep!() >>
    cond: map!(call!(Self::test_nocond), |e| *e) >>
    r: call!(Self::opt_comp_iter, { let mut acc = acc; acc.push(ComprehensionChunk::If { cond }); acc }) >> (
      r
    )
  )
);


// yield_expr: 'yield' [yield_arg]
// yield_arg: 'from' test | testlist
named!(pub yield_expr<StrSpan, Expression>,
  preceded!(
    tuple!(tag!("yield"), space_sep!()),
    alt!(
      preceded!(tuple!(tag!("from"), space_sep!()), call!(Self::test)) => { |e| Expression::YieldFrom(e) }
    | call!(Self::testlist) => { |e| Expression::Yield(e) }
    )
  )
);

} // End ExpressionParser

/*********************************************************************
 * Unit tests
 *********************************************************************/

#[cfg(test)]
mod tests {
    use nom;
    use helpers::{NewlinesAreNotSpaces, make_strspan, assert_parse_eq};
    use super::*;

    #[test]
    fn test_string() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;
        let new_pystring = |s: &str| PyString { prefix: "".to_string(), content: s.to_string() };
        assert_parse_eq(atom(make_strspan(r#""foo" "#)), Ok((make_strspan(" "),
            Box::new(Expression::String(vec![new_pystring("foo")])))
        ));
        assert_parse_eq(atom(make_strspan(r#""foo" "bar""#)), Ok((make_strspan(""),
            Box::new(Expression::String(vec![new_pystring("foo"), new_pystring("bar")])))
        ));
        assert_parse_eq(atom(make_strspan(r#""fo\"o" "#)), Ok((make_strspan(" "),
            Box::new(Expression::String(vec![new_pystring("fo\"o")])))
        ));
        assert_parse_eq(atom(make_strspan(r#""fo"o" "#)), Ok((make_strspan(r#"o" "#),
            Box::new(Expression::String(vec![new_pystring("fo")])))
        ));
        assert_parse_eq(atom(make_strspan(r#""fo \" o" "#)), Ok((make_strspan(" "),
            Box::new(Expression::String(vec![new_pystring("fo \" o")])))
        ));
        assert_parse_eq(atom(make_strspan(r#"'fo \' o' "#)), Ok((make_strspan(" "),
            Box::new(Expression::String(vec![new_pystring("fo ' o")])))
        ));
        assert_parse_eq(atom(make_strspan(r#"r'fo \' o' "#)), Ok((make_strspan(" "),
            Box::new(Expression::String(vec![PyString { prefix: "r".to_string(), content: "fo \\' o".to_string() }])))
        ));

        assert_parse_eq(atom(make_strspan(r#"'\x8a'"#)), Ok((make_strspan(""),
            Box::new(Expression::String(vec![new_pystring("\u{8a}")])))
        ));
    }

    #[test]
    fn test_triple_quotes_string() {
        let new_pystring = |s: &str| PyString { prefix: "".to_string(), content: s.to_string() };
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;
        assert_parse_eq(atom(make_strspan(r#"'''fo ' o''' "#)), Ok((make_strspan(" "), Box::new(Expression::String(vec![new_pystring("fo ' o")])))));
    }

    #[test]
    fn test_bytes() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;
        assert_parse_eq(atom(make_strspan(r#"b"foo" "#)), Ok((make_strspan(" "),
            Box::new(Expression::Bytes(b"foo".to_vec())))
        ));
        assert_parse_eq(atom(make_strspan(r#"b"foo" "bar""#)), Ok((make_strspan(""),
            Box::new(Expression::Bytes(b"foobar".to_vec())))
        ));
        assert_parse_eq(atom(make_strspan(r#"b"fo\"o" "#)), Ok((make_strspan(" "),
            Box::new(Expression::Bytes(b"fo\"o".to_vec())))
        ));
        assert_parse_eq(atom(make_strspan(r#"b"fo"o" "#)), Ok((make_strspan(r#"o" "#),
            Box::new(Expression::Bytes(b"fo".to_vec())))
        ));
        assert_parse_eq(atom(make_strspan(r#"b"fo \" o" "#)), Ok((make_strspan(" "),
            Box::new(Expression::Bytes(b"fo \" o".to_vec())))
        ));
        assert_parse_eq(atom(make_strspan(r#"b'fo \' o' "#)), Ok((make_strspan(" "),
            Box::new(Expression::Bytes(b"fo ' o".to_vec())))
        ));
        assert_parse_eq(atom(make_strspan(r#"br'fo \' o' "#)), Ok((make_strspan(" "),
            Box::new(Expression::Bytes(b"fo \\' o".to_vec())))
        ));
    }

    #[test]
    fn test_ternary() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;
        assert_parse_eq(test(make_strspan("foo if bar else baz")), Ok((make_strspan(""),
            Box::new(Expression::Ternary(
                Box::new(Expression::Name("foo".to_string())),
                Box::new(Expression::Name("bar".to_string())),
                Box::new(Expression::Name("baz".to_string())),
            ))
        )));
    }

    #[test]
    fn test_bool_ops() {
        let expr = ExpressionParser::<NewlinesAreNotSpaces>::expr;
        assert_parse_eq(expr(make_strspan("foo & bar | baz ^ qux")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::BitOr,
                Box::new(Expression::Bop(Bop::BitAnd,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Name("bar".to_string())),
                )),
                Box::new(Expression::Bop(Bop::BitXor,
                    Box::new(Expression::Name("baz".to_string())),
                    Box::new(Expression::Name("qux".to_string())),
                )),
            ))
        )));

        assert_parse_eq(expr(make_strspan("foo | bar & baz ^ qux")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::BitOr,
                Box::new(Expression::Name("foo".to_string())),
                Box::new(Expression::Bop(Bop::BitXor,
                    Box::new(Expression::Bop(Bop::BitAnd,
                        Box::new(Expression::Name("bar".to_string())),
                        Box::new(Expression::Name("baz".to_string())),
                    )),
                    Box::new(Expression::Name("qux".to_string())),
                )),
            ))
        )));
    }

    #[test]
    fn test_shift_expr() {
        let shift_expr = ExpressionParser::<NewlinesAreNotSpaces>::shift_expr;
        assert_parse_eq(shift_expr(make_strspan("foo << bar")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::Lshift,
                Box::new(Expression::Name("foo".to_string())),
                Box::new(Expression::Name("bar".to_string())),
            ))
        )));

        assert_parse_eq(shift_expr(make_strspan("foo >> bar")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::Rshift,
                Box::new(Expression::Name("foo".to_string())),
                Box::new(Expression::Name("bar".to_string())),
            ))
        )));
    }

    #[test]
    fn test_arith_expr() {
        let arith_expr = ExpressionParser::<NewlinesAreNotSpaces>::arith_expr;
        assert_parse_eq(arith_expr(make_strspan("foo + bar")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::Add,
                Box::new(Expression::Name("foo".to_string())),
                Box::new(Expression::Name("bar".to_string())),
            ))
        )));

        assert_parse_eq(arith_expr(make_strspan("foo * bar + baz")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::Add,
                Box::new(Expression::Bop(Bop::Mult,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Name("bar".to_string())),
                )),
                Box::new(Expression::Name("baz".to_string())),
            ))
        )));

        assert_parse_eq(arith_expr(make_strspan("foo + bar * baz")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::Add,
                Box::new(Expression::Name("foo".to_string())),
                Box::new(Expression::Bop(Bop::Mult,
                    Box::new(Expression::Name("bar".to_string())),
                    Box::new(Expression::Name("baz".to_string())),
                )),
            ))
        )));
    }

    #[test]
    fn test_term() {
        let term = ExpressionParser::<NewlinesAreNotSpaces>::term;
        assert_parse_eq(term(make_strspan("foo * bar")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::Mult,
                Box::new(Expression::Name("foo".to_string())),
                Box::new(Expression::Name("bar".to_string())),
            ))
        )));

        assert_parse_eq(term(make_strspan("foo ** bar * baz")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::Mult,
                Box::new(Expression::Bop(Bop::Power,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Name("bar".to_string())),
                )),
                Box::new(Expression::Name("baz".to_string())),
            ))
        )));

        assert_parse_eq(term(make_strspan("foo * bar ** baz")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::Mult,
                Box::new(Expression::Name("foo".to_string())),
                Box::new(Expression::Bop(Bop::Power,
                    Box::new(Expression::Name("bar".to_string())),
                    Box::new(Expression::Name("baz".to_string())),
                )),
            ))
        )));
    }

    #[test]
    fn test_power() {
        let factor = ExpressionParser::<NewlinesAreNotSpaces>::factor;
        assert_parse_eq(factor(make_strspan("foo ** bar")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::Power,
                Box::new(Expression::Name("foo".to_string())),
                Box::new(Expression::Name("bar".to_string())),
            ))
        )));

        assert_parse_eq(factor(make_strspan("foo ** + bar")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::Power,
                Box::new(Expression::Name("foo".to_string())),
                Box::new(Expression::Uop(Uop::Plus,
                    Box::new(Expression::Name("bar".to_string())),
                )),
            ))
        )));
    }

    #[test]
    fn test_bool() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;
        assert_parse_eq(test(make_strspan("foo and bar")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::And,
                Box::new(Expression::Name("foo".to_string())),
                Box::new(Expression::Name("bar".to_string())),
            ))
        )));

        assert_parse_eq(test(make_strspan("foo and + bar")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::And,
                Box::new(Expression::Name("foo".to_string())),
                Box::new(Expression::Uop(Uop::Plus,
                    Box::new(Expression::Name("bar".to_string())),
                )),
            ))
        )));
    }

    #[test]
    fn test_parentheses1() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;
        assert_parse_eq(test(make_strspan("(foo)")), Ok((make_strspan(""),
            Box::new(Expression::Name("foo".to_string())),
        )));
    }

    #[test]
    fn test_parentheses2() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;
        assert_parse_eq(test(make_strspan("(foo and bar)")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::And,
                Box::new(Expression::Name("foo".to_string())),
                Box::new(Expression::Name("bar".to_string())),
            ))
        )));
    }


    #[test]
    fn test_call_noarg() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(atom_expr(make_strspan("foo()")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
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
    fn test_call_positional_expr1() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(atom_expr(make_strspan("foo(bar and baz)")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Bop(Bop::And,
                                Box::new(Expression::Name("bar".to_string())),
                                Box::new(Expression::Name("baz".to_string())),
                            )
                        ),
                    ],
                    keyword_args: vec![
                    ],
                },
            ))
        )));
    }

    #[test]
    fn test_call_positional_expr2() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(atom_expr(make_strspan("foo(bar*baz)")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Bop(Bop::Mult,
                                Box::new(Expression::Name("bar".to_string())),
                                Box::new(Expression::Name("baz".to_string())),
                            )
                        ),
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
        assert_parse_eq(atom_expr(make_strspan("foo(bar)")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Name("bar".to_string())
                        ),
                    ],
                    keyword_args: vec![
                    ],
                },
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo(bar, baz)")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Name("bar".to_string())
                        ),
                        Argument::Normal(
                            Expression::Name("baz".to_string())
                        ),
                    ],
                    keyword_args: vec![
                    ],
                },
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo(bar, baz, *qux)")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Name("bar".to_string())
                        ),
                        Argument::Normal(
                            Expression::Name("baz".to_string())
                        ),
                        Argument::Star(
                            Expression::Name("qux".to_string())
                        ),
                    ],
                    keyword_args: vec![
                    ],
                },
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo(bar, *baz, qux)")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Name("bar".to_string())
                        ),
                        Argument::Star(
                            Expression::Name("baz".to_string())
                        ),
                        Argument::Normal(
                            Expression::Name("qux".to_string())
                        ),
                    ],
                    keyword_args: vec![
                    ],
                },
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo(bar, *baz, *qux)")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Name("bar".to_string())
                        ),
                        Argument::Star(
                            Expression::Name("baz".to_string())
                        ),
                        Argument::Star(
                            Expression::Name("qux".to_string())
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
        assert_parse_eq(atom_expr(make_strspan("foo(bar1=bar2)")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                    ],
                    keyword_args: vec![
                        Argument::Normal(
                            ("bar1".to_string(), Expression::Name("bar2".to_string())),
                        ),
                    ],
                },
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo(bar1=bar2, baz1=baz2)")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                    ],
                    keyword_args: vec![
                        Argument::Normal(
                            ("bar1".to_string(), Expression::Name("bar2".to_string())),
                        ),
                        Argument::Normal(
                            ("baz1".to_string(), Expression::Name("baz2".to_string())),
                        ),
                    ],
                },
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo(bar1=bar2, baz1=baz2, qux1=qux2)")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                    ],
                    keyword_args: vec![
                        Argument::Normal(
                            ("bar1".to_string(), Expression::Name("bar2".to_string())),
                        ),
                        Argument::Normal(
                            ("baz1".to_string(), Expression::Name("baz2".to_string())),
                        ),
                        Argument::Normal(
                            ("qux1".to_string(), Expression::Name("qux2".to_string())),
                        ),
                    ],
                },
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo(bar1=bar2, baz1=baz2, **qux)")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                    ],
                    keyword_args: vec![
                        Argument::Normal(
                            ("bar1".to_string(), Expression::Name("bar2".to_string())),
                        ),
                        Argument::Normal(
                            ("baz1".to_string(), Expression::Name("baz2".to_string())),
                        ),
                        Argument::Star(
                            Expression::Name("qux".to_string()),
                        ),
                    ],
                },
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo(bar1=bar2, **baz, **qux)")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                    ],
                    keyword_args: vec![
                        Argument::Normal(
                            ("bar1".to_string(), Expression::Name("bar2".to_string())),
                        ),
                        Argument::Star(
                            Expression::Name("baz".to_string()),
                        ),
                        Argument::Star(
                            Expression::Name("qux".to_string()),
                        ),
                    ],
                },
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo(bar1=bar2, **baz, qux1=qux2)")), Ok((make_strspan(""),
            Box::new(Expression::Call(
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                    ],
                    keyword_args: vec![
                        Argument::Normal(
                            ("bar1".to_string(), Expression::Name("bar2".to_string())),
                        ),
                        Argument::Star(
                            Expression::Name("baz".to_string()),
                        ),
                        Argument::Normal(
                            ("qux1".to_string(), Expression::Name("qux2".to_string())),
                        ),
                    ],
                },
            ))
        )));
    }

    #[test]
    fn call_badargs() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(atom_expr(make_strspan("foo(bar()=baz)")),
            Err(nom::Err::Failure(Context::Code(make_strspan(")"),
                ErrorKind::Custom(ArgumentError::KeywordExpression.into())
            )))
        );

        assert_parse_eq(atom_expr(make_strspan("foo(**baz, qux)")),
            Err(nom::Err::Failure(Context::Code(make_strspan(")"),
                ErrorKind::Custom(ArgumentError::PositionalAfterKeyword.into())
            )))
        );

        assert_parse_eq(atom_expr(make_strspan("foo(**baz, *qux)")),
            Err(nom::Err::Failure(Context::Code(make_strspan(")"),
                ErrorKind::Custom(ArgumentError::StarargsAfterKeyword.into())
            )))
        );

        assert_parse_eq(atom_expr(make_strspan("foo(bar1=bar2, qux)")),
            Err(nom::Err::Failure(Context::Code(make_strspan(")"),
                ErrorKind::Custom(ArgumentError::PositionalAfterKeyword.into())
            )))
        );

        assert_parse_eq(atom_expr(make_strspan("foo(bar1=bar2, *qux)")),
            Err(nom::Err::Failure(Context::Code(make_strspan(")"),
                ErrorKind::Custom(ArgumentError::StarargsAfterKeyword.into())
            )))
        );
    }

    #[test]
    fn test_subscript_simple() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(atom_expr(make_strspan("foo[bar]")), Ok((make_strspan(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Name("foo".to_string())),
                vec![
                    Subscript::Simple(
                        Expression::Name("bar".to_string()),
                    )
                ],
            ))
        )));
    }

    #[test]
    fn test_subscript_double() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(atom_expr(make_strspan("foo[bar:baz]")), Ok((make_strspan(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Name("foo".to_string())),
                vec![
                    Subscript::Double(
                        Some(Expression::Name("bar".to_string())),
                        Some(Expression::Name("baz".to_string())),
                    )
                ],
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo[bar:]")), Ok((make_strspan(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Name("foo".to_string())),
                vec![
                    Subscript::Double(
                        Some(Expression::Name("bar".to_string())),
                        None,
                    )
                ],
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo[:baz]")), Ok((make_strspan(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Name("foo".to_string())),
                vec![
                    Subscript::Double(
                        None,
                        Some(Expression::Name("baz".to_string())),
                    )
                ],
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo[:]")), Ok((make_strspan(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Name("foo".to_string())),
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
        assert_parse_eq(atom_expr(make_strspan("foo[bar:baz:qux]")), Ok((make_strspan(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Name("foo".to_string())),
                vec![
                    Subscript::Triple(
                        Some(Expression::Name("bar".to_string())),
                        Some(Expression::Name("baz".to_string())),
                        Some(Expression::Name("qux".to_string())),
                    )
                ],
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo[bar::qux]")), Ok((make_strspan(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Name("foo".to_string())),
                vec![
                    Subscript::Triple(
                        Some(Expression::Name("bar".to_string())),
                        None,
                        Some(Expression::Name("qux".to_string())),
                    )
                ],
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo[bar::]")), Ok((make_strspan(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Name("foo".to_string())),
                vec![
                    Subscript::Triple(
                        Some(Expression::Name("bar".to_string())),
                        None,
                        None,
                    )
                ],
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo[:baz:qux]")), Ok((make_strspan(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Name("foo".to_string())),
                vec![
                    Subscript::Triple(
                        None,
                        Some(Expression::Name("baz".to_string())),
                        Some(Expression::Name("qux".to_string())),
                    )
                ],
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo[:baz:]")), Ok((make_strspan(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Name("foo".to_string())),
                vec![
                    Subscript::Triple(
                        None,
                        Some(Expression::Name("baz".to_string())),
                        None,
                    )
                ],
            ))
        )));

        assert_parse_eq(atom_expr(make_strspan("foo[::]")), Ok((make_strspan(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Name("foo".to_string())),
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
        assert_parse_eq(atom_expr(make_strspan("foo.bar")), Ok((make_strspan(""),
            Box::new(Expression::Attribute(
                Box::new(Expression::Name("foo".to_string())),
                "bar".to_string(),
            ))
        )));
    }

    #[test]
    fn test_call_and_attribute() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(atom_expr(make_strspan("foo.bar().baz")), Ok((make_strspan(""),
            Box::new(Expression::Attribute(
                Box::new(Expression::Call(
                    Box::new(Expression::Attribute(
                        Box::new(Expression::Name("foo".to_string())),
                        "bar".to_string(),
                    )),
                    Arglist::default(),
                )),
                "baz".to_string(),
            ))
        )));
    }

    #[test]
    fn test_atom_expr() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(atom_expr(make_strspan("foo.bar[baz]")), Ok((make_strspan(""),
            Box::new(Expression::Subscript(
                Box::new(Expression::Attribute(
                    Box::new(Expression::Name("foo".to_string())),
                    "bar".to_string(),
                )),
                vec![
                    Subscript::Simple(
                        Expression::Name("baz".to_string()),
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
                Box::new(Expression::Name("foo".to_string())),
                Arglist {
                    positional_args: vec![
                        Argument::Normal(
                            Expression::Name("bar".to_string())
                        ),
                        Argument::Normal(
                            Expression::Bop(Bop::Add,
                                Box::new(Expression::Name("baz".to_string())),
                                Box::new(Expression::Name("qux".to_string())),
                            ),
                        ),
                    ],
                    keyword_args: vec![
                    ],
                },
            ));

        assert_parse_eq(atom_expr(make_strspan("foo(bar, baz + qux)")), Ok((make_strspan(""),
            ast.clone()
        )));

        assert_parse_eq(atom_expr(make_strspan("foo(bar, baz +\nqux)")), Ok((make_strspan(""),
            ast.clone()
        )));

        assert_parse_eq(atom_expr(make_strspan("foo(bar, baz +\n # foobar\nqux)")), Ok((make_strspan(""),
            ast
        )));
    }

    #[test]
    fn test_setlit() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;

        assert_parse_eq(atom(make_strspan("{foo}")), Ok((make_strspan(""),
            Box::new(Expression::SetLiteral(vec![
                SetItem::Unique(Expression::Name("foo".to_string())),
            ]))
        )));

        assert_parse_eq(atom(make_strspan("{foo, bar, baz}")), Ok((make_strspan(""),
            Box::new(Expression::SetLiteral(vec![
                SetItem::Unique(Expression::Name("foo".to_string())),
                SetItem::Unique(Expression::Name("bar".to_string())),
                SetItem::Unique(Expression::Name("baz".to_string())),
            ]))
        )));

        assert_parse_eq(atom(make_strspan("{foo, *bar, baz}")), Ok((make_strspan(""),
            Box::new(Expression::SetLiteral(vec![
                SetItem::Unique(Expression::Name("foo".to_string())),
                SetItem::Star(Expression::Name("bar".to_string())),
                SetItem::Unique(Expression::Name("baz".to_string())),
            ]))
        )));
    }

    #[test]
    fn test_setlit_comment() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;

        assert_parse_eq(atom(make_strspan("{foo, \n #bar\n\n\n baz}")), Ok((make_strspan(""),
            Box::new(Expression::SetLiteral(vec![
                SetItem::Unique(Expression::Name("foo".to_string())),
                SetItem::Unique(Expression::Name("baz".to_string())),
            ]))
        )));

        assert_parse_eq(atom(make_strspan("{\n #foo\n\n bar, baz}")), Ok((make_strspan(""),
            Box::new(Expression::SetLiteral(vec![
                SetItem::Unique(Expression::Name("bar".to_string())),
                SetItem::Unique(Expression::Name("baz".to_string())),
            ]))
        )));

        assert_parse_eq(atom(make_strspan("{ bar, baz \n}")), Ok((make_strspan(""),
            Box::new(Expression::SetLiteral(vec![
                SetItem::Unique(Expression::Name("bar".to_string())),
                SetItem::Unique(Expression::Name("baz".to_string())),
            ]))
        )));
    }

    #[test]
    fn test_dictlit() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;

        assert_parse_eq(atom(make_strspan("{}")), Ok((make_strspan(""), Box::new(
            Expression::DictLiteral(vec![
            ])
        ))));

        assert_parse_eq(atom(make_strspan("{foo1:foo2}")), Ok((make_strspan(""), Box::new(
            Expression::DictLiteral(vec![
                DictItem::Unique(
                    Expression::Name("foo1".to_string()),
                    Expression::Name("foo2".to_string()),
                ),
            ])
        ))));

        assert_parse_eq(atom(make_strspan("{foo1:foo2, bar1:bar2, baz1:baz2}")), Ok((make_strspan(""), Box::new(
            Expression::DictLiteral(vec![
                DictItem::Unique(
                    Expression::Name("foo1".to_string()),
                    Expression::Name("foo2".to_string()),
                ),
                DictItem::Unique(
                    Expression::Name("bar1".to_string()),
                    Expression::Name("bar2".to_string()),
                ),
                DictItem::Unique(
                    Expression::Name("baz1".to_string()),
                    Expression::Name("baz2".to_string()),
                ),
            ])
        ))));

        assert_parse_eq(atom(make_strspan("{foo1:foo2, **bar, baz1:baz2}")), Ok((make_strspan(""), Box::new(
            Expression::DictLiteral(vec![
                DictItem::Unique(
                    Expression::Name("foo1".to_string()),
                    Expression::Name("foo2".to_string()),
                ),
                DictItem::Star(Expression::Name("bar".to_string())),
                DictItem::Unique(
                    Expression::Name("baz1".to_string()),
                    Expression::Name("baz2".to_string()),
                ),
            ])
        ))));
    }

    #[test]
    fn test_comp_for() {
        let comp_for = ExpressionParser::<NewlinesAreNotSpaces>::comp_for;

        assert_parse_eq(comp_for(make_strspan("for bar in baz")), Ok((make_strspan(""), vec![
            ComprehensionChunk::For {
                async: false,
                item: vec![
                    Expression::Name("bar".to_string()),
                ],
                iterator: Expression::Name("baz".to_string()),
            },
        ])));
    }

    #[test]
    fn test_listcomp() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;

        assert_parse_eq(atom(make_strspan("[foo for bar in baz]")), Ok((make_strspan(""),
            Box::new(Expression::ListComp(
                Box::new(SetItem::Unique(Expression::Name("foo".to_string()))),
                vec![
                    ComprehensionChunk::For {
                        async: false,
                        item: vec![
                            Expression::Name("bar".to_string()),
                        ],
                        iterator: Expression::Name("baz".to_string()),
                    },
                ],
            ))
        )));
    }

    #[test]
    fn test_listcomp2() {
        let testlist_comp = ExpressionParser::<NewlinesAreNotSpaces>::testlist_comp;

        assert_parse_eq(testlist_comp(make_strspan("foo for bar in baz")), Ok((make_strspan(""),
            TestlistCompReturn::Comp(
                Box::new(SetItem::Unique(Expression::Name("foo".to_string()))),
                vec![
                    ComprehensionChunk::For {
                        async: false,
                        item: vec![
                            Expression::Name("bar".to_string()),
                        ],
                        iterator: Expression::Name("baz".to_string()),
                    },
                ],
            )
        )));
    }

    #[test]
    fn test_listcomp2_chain_for() {
        let testlist_comp = ExpressionParser::<NewlinesAreNotSpaces>::testlist_comp;

        assert_parse_eq(testlist_comp(make_strspan("foo for bar in baz for qux in quux")), Ok((make_strspan(""),
            TestlistCompReturn::Comp(
                Box::new(SetItem::Unique(Expression::Name("foo".to_string()))),
                vec![
                    ComprehensionChunk::For {
                        async: false,
                        item: vec![
                            Expression::Name("bar".to_string()),
                        ],
                        iterator: Expression::Name("baz".to_string()),
                    },
                    ComprehensionChunk::For {
                        async: false,
                        item: vec![
                            Expression::Name("qux".to_string()),
                        ],
                        iterator: Expression::Name("quux".to_string()),
                    },
                ],
            )
        )));
    }

    #[test]
    fn test_listcomp2_chain_if() {
        let testlist_comp = ExpressionParser::<NewlinesAreNotSpaces>::testlist_comp;

        assert_parse_eq(testlist_comp(make_strspan("foo for bar in baz if qux")), Ok((make_strspan(""),
            TestlistCompReturn::Comp(
                Box::new(SetItem::Unique(Expression::Name("foo".to_string()))),
                vec![
                    ComprehensionChunk::For {
                        async: false,
                        item: vec![
                            Expression::Name("bar".to_string()),
                        ],
                        iterator: Expression::Name("baz".to_string()),
                    },
                    ComprehensionChunk::If {
                        cond: Expression::Name("qux".to_string()),
                    },
                ],
            )
        )));
    }

    #[test]
    fn test_setcomp() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;

        assert_parse_eq(atom(make_strspan("{foo for bar in baz}")), Ok((make_strspan(""), Box::new(
            Expression::SetComp(
                Box::new(SetItem::Unique(Expression::Name("foo".to_string()))),
                vec![
                    ComprehensionChunk::For {
                        async: false,
                        item: vec![
                            Expression::Name("bar".to_string()),
                        ],
                        iterator: Expression::Name("baz".to_string()),
                    },
                ]
            )
        ))));
    }


    #[test]
    fn test_op() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;
        assert_parse_eq(test(make_strspan("n >= 0")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::Geq,
                Box::new(Expression::Name("n".to_string())),
                Box::new(Expression::Int(0u32.into()))
            ))
        )));
    }

    #[test]
    fn test_lambda() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;

        assert_parse_eq(test(make_strspan("lambda: foo")), Ok((make_strspan(""),
            Box::new(Expression::Lambdef(
                Default::default(),
                Box::new(Expression::Name("foo".to_string())),
            ))
        )));

        assert_parse_eq(test(make_strspan("lambda : foo")), Ok((make_strspan(""),
            Box::new(Expression::Lambdef(
                Default::default(),
                Box::new(Expression::Name("foo".to_string())),
            ))
        )));

        assert_parse_eq(test(make_strspan("lambda :foo")), Ok((make_strspan(""),
            Box::new(Expression::Lambdef(
                Default::default(),
                Box::new(Expression::Name("foo".to_string())),
            ))
        )));
    }

    #[test]
    fn test_multibop() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;

        assert_parse_eq(test(make_strspan("a <= b < c")), Ok((make_strspan(""),
            Box::new(Expression::MultiBop(
                Box::new(Expression::Name("a".to_string())),
                vec![
                    (Bop::Leq, Expression::Name("b".to_string())),
                    (Bop::Lt, Expression::Name("c".to_string())),
                ]
            ))
        )));
    }


    #[test]
    fn test_escaped_newline() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;

        assert_parse_eq(test(make_strspan("a <= \\\nb")), Ok((make_strspan(""),
            Box::new(Expression::Bop(Bop::Leq,
                Box::new(Expression::Name("a".to_string())),
                Box::new(Expression::Name("b".to_string())),
            ))
        )));
    }
}
