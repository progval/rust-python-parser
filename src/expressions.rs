use std::marker::PhantomData;

use ast::*;
use bytes::bytes;
use functions::varargslist;
use helpers::*;
use numbers::number;
use strings::string;

#[derive(Clone, Debug, PartialEq)]
enum TestlistCompReturn {
    Comp(Box<SetItem>, Vec<ComprehensionChunk>), // comprehension
    Lit(Vec<SetItem>),                           // list of litterals (length >= 1)
    Single(SetItem), // a single litteral: either from `[foo]` (list) or `(foo)` (atom, NOT tuple)
}

pub(crate) struct ExpressionParser<ANS: AreNewlinesSpaces> {
    _phantom: PhantomData<ANS>,
}

impl<ANS: AreNewlinesSpaces> ExpressionParser<ANS> {
    /*********************************************************************
     * Decorators
     *********************************************************************/

    // namedexpr_test: test [':=' test]
    named!(pub namedexpr_test<StrSpan, Box<Expression>>,
      do_parse!(
        left: call!(Self::test) >>
        right: opt!(
          preceded!(
            ws_auto!(keyword!(":=")),
            call!(Self::test)
          )
        ) >> (
          match right {
            None => left,
            Some(right) => Box::new(Expression::Named(left, right)),
          }
        )
      )
    );

    // test: or_test ['if' or_test 'else' test] | lambdef
    named!(pub test<StrSpan, Box<Expression>>,
      alt!(
        call!(Self::lambdef)
      | do_parse!(
          left: call!(Self::or_test) >>
          right: opt!(do_parse!(
            ws_auto!(keyword!("if")) >>
            cond: return_error!(call!(Self::or_test)) >>
            ws_auto!(keyword!("else")) >>
            right: return_error!(call!(Self::test)) >> (
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
      ws_auto!(preceded!(keyword!("lambda"), return_error!(do_parse!(
        args: opt!(varargslist) >>
        spaces!() >>
        char!(':') >>
        spaces!() >>
        code: call!(Self::test) >> (
          Box::new(Expression::Lambdef(args.unwrap_or_default(), code))
        )
      ))))
    );

    // lambdef_nocond: 'lambda' [varargslist] ':' test_nocond
    named!(lambdef_nocond<StrSpan, Box<Expression>>,
      ws_auto!(preceded!(keyword!("lambda"), return_error!(do_parse!(
        args: opt!(varargslist) >>
        char!(':') >>
        code: call!(Self::test_nocond) >> (
          Box::new(Expression::Lambdef(args.unwrap_or_default(), code))
        )
      ))))
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
    bop!(
        or_test,
        Self::and_test,
        alt!(
          keyword!("or") => { |_| Bop::Or }
        )
    );

    // and_test: not_test ('and' not_test)*
    bop!(
        and_test,
        Self::not_test,
        alt!(
          keyword!("and") => { |_| Bop::And }
        )
    );

    // not_test: 'not' not_test | comparison
    named!(not_test<StrSpan, Box<Expression>>,
      alt!(
        preceded!(tuple!(keyword!("not"), spaces!()), call!(Self::not_test)) => { |e| Box::new(Expression::Uop(Uop::Not, e)) }
      | call!(Self::comparison)
      )
    );

    // comparison: expr (comp_op expr)*
    // comp_op: '<'|'>'|'=='|'>='|'<='|'<>'|'!='|'in'|'not' 'in'|'is'|'is' 'not'
    bop!(
        comparison,
        Self::expr,
        alt!(
          tag!("==") => { |_| Bop::Eq }
        | tag!("<=") => { |_| Bop::Leq }
        | tag!(">=") => { |_| Bop::Geq }
        | char!('<') => { |_| Bop::Lt }
        | char!('>') => { |_| Bop::Gt }
        | tag!("!=") => { |_| Bop::Neq }
        | tag!("in") => { |_| Bop::In }
        | tuple!(tag!("not"), space_sep!(), keyword!("in")) => { |_| Bop::NotIn }
        | tuple!(tag!("is"), space_sep!(), keyword!("not")) => { |_| Bop::IsNot }
        | tuple!(tag!("is"), space_sep!()) => { |_| Bop::Is }
        )
    );

    // star_expr: '*' expr
    named!(pub star_expr<StrSpan, Box<Expression>>,
     do_parse!(char!('*') >> spaces!() >> e: call!(Self::expr) >> (Box::new(Expression::Star(e))))
    );

    // expr: xor_expr ('|' xor_expr)*
    bop!(
        expr,
        Self::xor_expr,
        alt!(
          char!('|') => { |_| Bop::BitOr }
        )
    );

    // xor_expr: and_expr ('^' and_expr)*
    bop!(
        xor_expr,
        Self::and_expr,
        alt!(
          char!('^') => { |_| Bop::BitXor }
        )
    );

    // and_expr: shift_expr ('&' shift_expr)*
    bop!(
        and_expr,
        Self::shift_expr,
        alt!(
          char!('&') => { |_| Bop::BitAnd }
        )
    );

    // shift_expr: arith_expr (('<<'|'>>') arith_expr)*
    bop!(
        shift_expr,
        Self::arith_expr,
        alt!(
          tag!("<<") => { |_| Bop::Lshift }
        | tag!(">>") => { |_| Bop::Rshift }
        )
    );

    // arith_expr: term (('+'|'-') term)*
    bop!(
        arith_expr,
        Self::term,
        alt!(
          char!('+') => { |_| Bop::Add }
        | char!('-') => { |_| Bop::Sub }
        )
    );

    // term: factor (('*'|'@'|'/'|'%'|'//') factor)*
    bop!(
        term,
        Self::factor,
        alt!(
          char!('*') => { |_| Bop::Mult }
        | char!('@') => { |_| Bop::Matmult }
        | char!('%') => { |_| Bop::Mod }
        | tag!("//") => { |_| Bop::Floordiv }
        | char!('/') => { |_| Bop::Div }
        )
    );

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
enum Trailer {
    Call(Vec<Argument>),
    Subscript(Vec<Subscript>),
    Attribute(Name),
}
impl<ANS: AreNewlinesSpaces> ExpressionParser<ANS> {
    // atom_expr: ['await'] atom trailer*
    // trailer: '(' [arglist] ')' | '[' subscriptlist ']' | '.' NAME
    // subscriptlist: subscript (',' subscript)* [',']
    named!(atom_expr<StrSpan, Box<Expression>>,
      do_parse!(
        async: map!(opt!(terminated!(tag!("await"), space_sep!())), |o| o.is_some()) >>
        lhs: call!(Self::atom) >>
        trailers: fold_many0!(
          ws_auto!(alt!(
            delimited!(char!('('), ws_comm!(call!(ExpressionParser::<NewlinesAreSpaces>::arglist)), char!(')')) => { |args| Trailer::Call(args) }
          | delimited!(char!('['), ws_comm!(separated_list!(char!(','), call!(ExpressionParser::<NewlinesAreSpaces>::subscript))), char!(']')) => { |i| Trailer::Subscript(i) }
          | preceded!(ws_auto!(char!('.')), name) => { |name| Trailer::Attribute(name) }
          )),
          lhs,
          |acc, item| Box::new(match item {
            Trailer::Call(args) => Expression::Call(acc, args),
            Trailer::Subscript(i) => Expression::Subscript(acc, i),
            Trailer::Attribute(name) => Expression::Attribute(acc, name),
          })
        ) >> (
          if async { Box::new(Expression::Await(trailers)) } else { trailers }
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
      | keyword!("None") => { |_| Expression::None }
      | keyword!("True") => { |_| Expression::True }
      | keyword!("False") => { |_| Expression::False }
      | separated_nonempty_list!(spaces!(), string) => { |s| Expression::String(s) }
      | separated_nonempty_list!(spaces!(), bytes) => { |v| {
          let mut v2 = Vec::new();
          for b in v { v2.extend(b) }
          Expression::Bytes(v2)
        }}
      | number
      | name => { |n| Expression::Name(n) }
      | tuple!(char!('['), ws_comm!(opt!(char!(' '))), char!(']')) => { |_| Expression::ListLiteral(vec![]) }
      | tuple!(char!('{'), ws_comm!(opt!(char!(' '))), char!('}')) => { |_| Expression::DictLiteral(vec![]) }
      | tuple!(char!('('), ws_comm!(opt!(char!(' '))), char!(')')) => { |_| Expression::TupleLiteral(vec![]) }
      | delimited!(char!('{'), ws_comm!(map!(
          call!(ExpressionParser::<NewlinesAreSpaces>::dictorsetmaker), |e:Box<_>| *e
        )), char!('}'))
      | map_opt!(ws_auto!(delimited!(char!('('), ws_comm!(
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
      | delimited!(char!('('), ws_comm!(
          call!(ExpressionParser::<NewlinesAreSpaces>::yield_expr)
        ), char!(')'))
      | delimited!(char!('['), ws_comm!(
          call!(ExpressionParser::<NewlinesAreSpaces>::testlist_comp)
        ), char!(']')) => { |ret| {
          match ret {
              TestlistCompReturn::Comp(e, comp) => Expression::ListComp(e, comp),
              TestlistCompReturn::Lit(v) => Expression::ListLiteral(v),
              TestlistCompReturn::Single(e) => Expression::ListLiteral(vec![e]),
          }}
        }
      ), |e| Box::new(e))
    );

    // testlist_comp: (namedexpr_test|star_expr) ( comp_for | (',' (namedexpr_test|star_expr))* [','] )
    named!(testlist_comp<StrSpan, TestlistCompReturn>,
      do_parse!(
        first: ws_auto!(alt!(
            call!(Self::namedexpr_test) => { |e: Box<_>| SetItem::Unique(*e) }
          | preceded!(char!('*'), call!(Self::expr)) => { |e: Box<_>| SetItem::Star(*e) }
          )) >>
        r: alt!(
          call!(Self::comp_for) => { |comp| TestlistCompReturn::Comp(Box::new(first), comp) }
        | opt!(delimited!(
            ws_auto!(char!(',')),
            separated_list!(ws_auto!(char!(',')),
              alt!(
                call!(Self::namedexpr_test) => { |e: Box<_>| SetItem::Unique(*e) }
              | preceded!(char!('*'), call!(Self::expr)) => { |e: Box<_>| SetItem::Star(*e) }
              )
            ),
            ws_auto!(opt!(char!(',')))
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
      ws_comm!(alt!(
        preceded!(char!(':'), call!(Self::subscript_trail, None))
      | do_parse!(
          first: call!(Self::test) >>
          r: opt!(ws_comm!(preceded!(char!(':'), call!(Self::subscript_trail, Some(*first.clone()))))) >> ( // FIXME: remove this clone
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
      separated_nonempty_list!(ws_auto!(char!(',')), map!(alt!(call!(Self::expr)|call!(Self::star_expr)), |e| *e))
    );

    // testlist: test (',' test)* [',']
    named!(pub testlist<StrSpan, Vec<Expression>>,
      separated_nonempty_list!(ws_auto!(char!(',')), map!(call!(Self::test), |e| *e))
    );

    // FIXME: the code of this function is unreadable
    named!(pub possibly_empty_testlist<StrSpan, Vec<Expression>>,
      alt!(
        tuple!(separated_nonempty_list!(ws_auto!(char!(',')), map!(call!(Self::test), |e:Box<_>| *e)), opt!(ws_auto!(char!(',')))) => { |(mut e, comma):(Vec<_>, _)|
          match (e.len(), comma) {
              (0, _) => unreachable!(),
              (1, Some(_)) => vec![Expression::TupleLiteral(vec![SetItem::Unique(e.remove(0))])], // The remove can't panic, because len == 1
              (1, None) => vec![e.remove(0)], // The remove can't panic, because len == 1
              (_, _) => e,
          }
        }
      | tag!("") => { |_| Vec::new() }
      )
    );

    // testlist_star_expr: (test|star_expr) (',' (test|star_expr))* [',']
    named!(pub testlist_star_expr<StrSpan, Vec<Expression>>,
      do_parse!(
        list: separated_nonempty_list!(
          ws_auto!(char!(',')),
          map!(alt!(
            call!(Self::test)
          | call!(Self::star_expr)
          ), |e| *e)
        ) >>
        trailing_comma: opt!(ws_auto!(char!(','))) >> (
          if trailing_comma.is_some() && list.len() < 2 {
              // This prevents "foo, =" from being parsed as "foo ="
              vec![Expression::TupleLiteral(list.into_iter().map(SetItem::Unique).collect())]
          }
          else {
              list
          }
        )
      )
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
      ws_comm!(alt!(
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
          ws_comm!(delimited!(char!(','), separated_list!(char!(','), call!(Self::dictitem)), opt!(ws_comm!(char!(','))))) => { |v: Vec<_>| {
            let mut v = v;
            v.insert(0, item1.clone()); // FIXME: do not clone
            Box::new(Expression::DictLiteral(v))
          }}
        | preceded!(peek!(keyword!("for")), return_error!(call!(Self::comp_for))) => { |comp| {
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
          ws_comm!(delimited!(char!(','), separated_list!(char!(','), call!(Self::setitem)), opt!(ws_comm!(char!(','))))) => { |v: Vec<_>| {
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
      ws_comm!(alt!(
        preceded!(tag!("**"), call!(Self::expr)) => { |e:Box<_>| DictItem::Star(*e) }
      | tuple!(call!(Self::test), char!(':'), call!(Self::test)) => { |(e1,_,e2): (Box<_>,_,Box<_>)| DictItem::Unique(*e1,*e2) }
      ))
    );

    named!(setitem<StrSpan, SetItem>,
      ws_comm!(alt!(
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
    named!(pub arglist<StrSpan, Vec<Argument>>,
      ws_comm!(do_parse!(
        args: separated_list!(ws_comm!(char!(',')),
          alt!(
            preceded!(tag!("**"), call!(Self::test)) => { |kwargs: Box<_>| Argument::Kwargs(*kwargs) }
          | preceded!(char!('*'), call!(Self::test)) => { |args: Box<_>| Argument::Starargs(*args) }
          | do_parse!(
              name: name >> // According to the grammar, this should be a 'test', but cpython actually refuses it (for good reasons)
              value: preceded!(char!('='), call!(Self::test)) >> (
                Argument::Keyword(name.to_string(), *value)
              )
            )
          | do_parse!(
              test1: call!(Self::test) >>
              next: opt!(ws_comm!(alt!(call!(Self::comp_for)))) >> (
                match next {
                    Some(e) => Argument::Positional(Expression::Generator(Box::new(SetItem::Unique(*test1)), e)),
                    None => Argument::Positional(*test1)
                }
              )
            )
          )
        ) >>
        opt!(ws_comm!(char!(','))) >>
        (args)
      ))
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
      return_error!(map!(opt!(call!(Self::comp_iter, acc.clone())), |r| r.unwrap_or(acc))) // FIXME: do not clone
    );

    // sync_comp_for: 'for' exprlist 'in' or_test [comp_iter]
    // comp_for: ['async'] sync_comp_for
    named!(comp_for<StrSpan, Vec<ComprehensionChunk>>,
      call!(Self::comp_for2, Vec::new())
    );
    named_args!(comp_for2(acc: Vec<ComprehensionChunk>) <StrSpan, Vec<ComprehensionChunk>>,
      do_parse!(
        async: map!(opt!(terminated!(tag!("async"), space_sep!())), |o| o.is_some()) >>
        keyword!("for") >>
        spaces!() >>
        item: return_error!(call!(Self::exprlist)) >>
        spaces!() >>
        keyword!("in") >>
        spaces!() >>
        iterator: return_error!(map!(call!(Self::or_test), |e| *e)) >>
        spaces!() >>
        r: call!(Self::opt_comp_iter, { let mut acc = acc; acc.push(ComprehensionChunk::For { async, item, iterator }); acc }) >> (
          r
        )
      )
    );

    // comp_if: 'if' test_nocond [comp_iter]
    named_args!(comp_if(acc: Vec<ComprehensionChunk>) <StrSpan, Vec<ComprehensionChunk>>,
      do_parse!(
        keyword!("if") >>
        spaces!() >>
        cond: return_error!(map!(call!(Self::test_nocond), |e| *e)) >>
        spaces!() >>
        r: call!(Self::opt_comp_iter, { let mut acc = acc; acc.push(ComprehensionChunk::If { cond }); acc }) >> (
          r
        )
      )
    );

    // yield_expr: 'yield' [yield_arg]
    // yield_arg: 'from' test | testlist_star_expr
    named!(pub yield_expr<StrSpan, Expression>,
      ws_auto!(preceded!(
        keyword!("yield"),
        ws_auto!(alt!(
          preceded!(ws_auto!(keyword!("from")), call!(Self::test)) => { |e| Expression::YieldFrom(e) }
        | call!(Self::testlist_star_expr) => { |e| Expression::Yield(e) }
        | tag!("") => { |_| Expression::Yield(Vec::new()) }
        ))
      ))
    );
} // End ExpressionParser

/*********************************************************************
 * Unit tests
 *********************************************************************/

#[cfg(test)]
mod tests {
    use super::*;
    use helpers::{assert_parse_eq, make_strspan, NewlinesAreNotSpaces};

    #[cfg(feature = "wtf8")]
    fn new_pystring(prefix: &str, s: &str) -> PyString {
        PyString {
            prefix: prefix.to_string(),
            content: PyStringContent::from_str(s),
        }
    }

    #[cfg(not(feature = "wtf8"))]
    fn new_pystring(prefix: &str, s: &str) -> PyString {
        PyString {
            prefix: prefix.to_string(),
            content: s.to_string(),
        }
    }

    #[test]
    fn test_string() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;
        assert_parse_eq(
            atom(make_strspan(r#""foo" "#)),
            Ok((
                make_strspan(" "),
                Box::new(Expression::String(vec![new_pystring("", "foo")])),
            )),
        );
        assert_parse_eq(
            atom(make_strspan(r#""foo" "bar""#)),
            Ok((
                make_strspan(""),
                Box::new(Expression::String(vec![
                    new_pystring("", "foo"),
                    new_pystring("", "bar"),
                ])),
            )),
        );
        assert_parse_eq(
            atom(make_strspan(r#""fo\"o" "#)),
            Ok((
                make_strspan(" "),
                Box::new(Expression::String(vec![new_pystring("", "fo\"o")])),
            )),
        );
        assert_parse_eq(
            atom(make_strspan(r#""fo"o" "#)),
            Ok((
                make_strspan(r#"o" "#),
                Box::new(Expression::String(vec![new_pystring("", "fo")])),
            )),
        );
        assert_parse_eq(
            atom(make_strspan(r#""fo \" o" "#)),
            Ok((
                make_strspan(" "),
                Box::new(Expression::String(vec![new_pystring("", "fo \" o")])),
            )),
        );
        assert_parse_eq(
            atom(make_strspan(r#"'fo \' o' "#)),
            Ok((
                make_strspan(" "),
                Box::new(Expression::String(vec![new_pystring("", "fo ' o")])),
            )),
        );
        assert_parse_eq(
            atom(make_strspan(r#"r'fo \' o' "#)),
            Ok((
                make_strspan(" "),
                Box::new(Expression::String(vec![new_pystring("r", "fo \\' o")])),
            )),
        );

        assert_parse_eq(
            atom(make_strspan(r#"'\x8a'"#)),
            Ok((
                make_strspan(""),
                Box::new(Expression::String(vec![new_pystring("", "\u{8a}")])),
            )),
        );
    }

    #[test]
    #[cfg_attr(not(feature = "unicode-names"), ignore)]
    fn test_unicode_name() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;
        assert_parse_eq(
            atom(make_strspan(r#"'\N{snowman}'"#)),
            Ok((
                make_strspan(""),
                Box::new(Expression::String(vec![new_pystring("", "☃")])),
            )),
        );
    }

    #[test]
    fn test_triple_quotes_string() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;
        assert_parse_eq(
            atom(make_strspan(r#"'''fo ' o''' "#)),
            Ok((
                make_strspan(" "),
                Box::new(Expression::String(vec![new_pystring("", "fo ' o")])),
            )),
        );
    }

    #[test]
    fn test_bytes() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;
        assert_parse_eq(
            atom(make_strspan(r#"b"foo" "#)),
            Ok((
                make_strspan(" "),
                Box::new(Expression::Bytes(b"foo".to_vec())),
            )),
        );
        assert_parse_eq(
            atom(make_strspan(r#"b"foo" "bar""#)),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bytes(b"foobar".to_vec())),
            )),
        );
        assert_parse_eq(
            atom(make_strspan(r#"b"fo\"o" "#)),
            Ok((
                make_strspan(" "),
                Box::new(Expression::Bytes(b"fo\"o".to_vec())),
            )),
        );
        assert_parse_eq(
            atom(make_strspan(r#"b"fo"o" "#)),
            Ok((
                make_strspan(r#"o" "#),
                Box::new(Expression::Bytes(b"fo".to_vec())),
            )),
        );
        assert_parse_eq(
            atom(make_strspan(r#"b"fo \" o" "#)),
            Ok((
                make_strspan(" "),
                Box::new(Expression::Bytes(b"fo \" o".to_vec())),
            )),
        );
        assert_parse_eq(
            atom(make_strspan(r#"b'fo \' o' "#)),
            Ok((
                make_strspan(" "),
                Box::new(Expression::Bytes(b"fo ' o".to_vec())),
            )),
        );
        assert_parse_eq(
            atom(make_strspan(r#"br'fo \' o' "#)),
            Ok((
                make_strspan(" "),
                Box::new(Expression::Bytes(b"fo \\' o".to_vec())),
            )),
        );
    }

    #[test]
    fn test_ternary() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;
        assert_parse_eq(
            test(make_strspan("foo if bar else baz")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Ternary(
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Name("bar".to_string())),
                    Box::new(Expression::Name("baz".to_string())),
                )),
            )),
        );
    }

    #[test]
    fn test_bool_ops() {
        let expr = ExpressionParser::<NewlinesAreNotSpaces>::expr;
        assert_parse_eq(
            expr(make_strspan("foo & bar | baz ^ qux")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::BitOr,
                    Box::new(Expression::Bop(
                        Bop::BitAnd,
                        Box::new(Expression::Name("foo".to_string())),
                        Box::new(Expression::Name("bar".to_string())),
                    )),
                    Box::new(Expression::Bop(
                        Bop::BitXor,
                        Box::new(Expression::Name("baz".to_string())),
                        Box::new(Expression::Name("qux".to_string())),
                    )),
                )),
            )),
        );

        assert_parse_eq(
            expr(make_strspan("foo | bar & baz ^ qux")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::BitOr,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Bop(
                        Bop::BitXor,
                        Box::new(Expression::Bop(
                            Bop::BitAnd,
                            Box::new(Expression::Name("bar".to_string())),
                            Box::new(Expression::Name("baz".to_string())),
                        )),
                        Box::new(Expression::Name("qux".to_string())),
                    )),
                )),
            )),
        );
    }

    #[test]
    fn test_shift_expr() {
        let shift_expr = ExpressionParser::<NewlinesAreNotSpaces>::shift_expr;
        assert_parse_eq(
            shift_expr(make_strspan("foo << bar")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::Lshift,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Name("bar".to_string())),
                )),
            )),
        );

        assert_parse_eq(
            shift_expr(make_strspan("foo >> bar")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::Rshift,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Name("bar".to_string())),
                )),
            )),
        );
    }

    #[test]
    fn test_arith_expr() {
        let arith_expr = ExpressionParser::<NewlinesAreNotSpaces>::arith_expr;
        assert_parse_eq(
            arith_expr(make_strspan("foo + bar")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::Add,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Name("bar".to_string())),
                )),
            )),
        );

        assert_parse_eq(
            arith_expr(make_strspan("foo * bar + baz")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::Add,
                    Box::new(Expression::Bop(
                        Bop::Mult,
                        Box::new(Expression::Name("foo".to_string())),
                        Box::new(Expression::Name("bar".to_string())),
                    )),
                    Box::new(Expression::Name("baz".to_string())),
                )),
            )),
        );

        assert_parse_eq(
            arith_expr(make_strspan("foo + bar * baz")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::Add,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Bop(
                        Bop::Mult,
                        Box::new(Expression::Name("bar".to_string())),
                        Box::new(Expression::Name("baz".to_string())),
                    )),
                )),
            )),
        );
    }

    #[test]
    fn test_term() {
        let term = ExpressionParser::<NewlinesAreNotSpaces>::term;
        assert_parse_eq(
            term(make_strspan("foo * bar")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::Mult,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Name("bar".to_string())),
                )),
            )),
        );

        assert_parse_eq(
            term(make_strspan("foo ** bar * baz")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::Mult,
                    Box::new(Expression::Bop(
                        Bop::Power,
                        Box::new(Expression::Name("foo".to_string())),
                        Box::new(Expression::Name("bar".to_string())),
                    )),
                    Box::new(Expression::Name("baz".to_string())),
                )),
            )),
        );

        assert_parse_eq(
            term(make_strspan("foo * bar ** baz")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::Mult,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Bop(
                        Bop::Power,
                        Box::new(Expression::Name("bar".to_string())),
                        Box::new(Expression::Name("baz".to_string())),
                    )),
                )),
            )),
        );
    }

    #[test]
    fn test_power() {
        let factor = ExpressionParser::<NewlinesAreNotSpaces>::factor;
        assert_parse_eq(
            factor(make_strspan("foo ** bar")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::Power,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Name("bar".to_string())),
                )),
            )),
        );

        assert_parse_eq(
            factor(make_strspan("foo ** + bar")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::Power,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Uop(
                        Uop::Plus,
                        Box::new(Expression::Name("bar".to_string())),
                    )),
                )),
            )),
        );
    }

    #[test]
    fn test_bool() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;
        assert_parse_eq(
            test(make_strspan("foo and bar")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::And,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Name("bar".to_string())),
                )),
            )),
        );

        assert_parse_eq(
            test(make_strspan("foo and + bar")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::And,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Uop(
                        Uop::Plus,
                        Box::new(Expression::Name("bar".to_string())),
                    )),
                )),
            )),
        );
    }

    #[test]
    fn test_not() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;
        assert_parse_eq(
            test(make_strspan("not foo")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Uop(
                    Uop::Not,
                    Box::new(Expression::Name("foo".to_string())),
                )),
            )),
        );

        assert_parse_eq(
            test(make_strspan("not not foo")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Uop(
                    Uop::Not,
                    Box::new(Expression::Uop(
                        Uop::Not,
                        Box::new(Expression::Name("foo".to_string())),
                    )),
                )),
            )),
        );
    }

    #[test]
    fn test_parentheses1() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;
        assert_parse_eq(
            test(make_strspan("(foo)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Name("foo".to_string())),
            )),
        );
    }

    #[test]
    fn test_parentheses2() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;
        assert_parse_eq(
            test(make_strspan("(foo and bar)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::And,
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Name("bar".to_string())),
                )),
            )),
        );
    }

    #[test]
    fn test_call_noarg() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(
            atom_expr(make_strspan("foo()")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![],
                )),
            )),
        );
    }

    #[test]
    fn test_call_positional_expr1() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(
            atom_expr(make_strspan("foo(bar and baz)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Argument::Positional(Expression::Bop(
                        Bop::And,
                        Box::new(Expression::Name("bar".to_string())),
                        Box::new(Expression::Name("baz".to_string())),
                    ))],
                )),
            )),
        );
    }

    #[test]
    fn test_call_positional_expr2() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(
            atom_expr(make_strspan("foo(bar*baz)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Argument::Positional(Expression::Bop(
                        Bop::Mult,
                        Box::new(Expression::Name("bar".to_string())),
                        Box::new(Expression::Name("baz".to_string())),
                    ))],
                )),
            )),
        );
    }

    #[test]
    fn test_call_positional() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(
            atom_expr(make_strspan("foo(bar)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Argument::Positional(Expression::Name("bar".to_string()))],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo(bar, baz)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![
                        Argument::Positional(Expression::Name("bar".to_string())),
                        Argument::Positional(Expression::Name("baz".to_string())),
                    ],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo(bar, baz, *qux)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![
                        Argument::Positional(Expression::Name("bar".to_string())),
                        Argument::Positional(Expression::Name("baz".to_string())),
                        Argument::Starargs(Expression::Name("qux".to_string())),
                    ],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo(bar, *baz, qux)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![
                        Argument::Positional(Expression::Name("bar".to_string())),
                        Argument::Starargs(Expression::Name("baz".to_string())),
                        Argument::Positional(Expression::Name("qux".to_string())),
                    ],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo(bar, *baz, *qux)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![
                        Argument::Positional(Expression::Name("bar".to_string())),
                        Argument::Starargs(Expression::Name("baz".to_string())),
                        Argument::Starargs(Expression::Name("qux".to_string())),
                    ],
                )),
            )),
        );
    }

    #[test]
    fn test_call_keyword() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(
            atom_expr(make_strspan("foo(bar1=bar2)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Argument::Keyword(
                        "bar1".to_string(),
                        Expression::Name("bar2".to_string()),
                    )],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo(bar1=bar2, baz1=baz2)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![
                        Argument::Keyword("bar1".to_string(), Expression::Name("bar2".to_string())),
                        Argument::Keyword("baz1".to_string(), Expression::Name("baz2".to_string())),
                    ],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo(bar1=bar2, baz1=baz2, qux1=qux2)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![
                        Argument::Keyword("bar1".to_string(), Expression::Name("bar2".to_string())),
                        Argument::Keyword("baz1".to_string(), Expression::Name("baz2".to_string())),
                        Argument::Keyword("qux1".to_string(), Expression::Name("qux2".to_string())),
                    ],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo(bar1=bar2, baz1=baz2, **qux)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![
                        Argument::Keyword("bar1".to_string(), Expression::Name("bar2".to_string())),
                        Argument::Keyword("baz1".to_string(), Expression::Name("baz2".to_string())),
                        Argument::Kwargs(Expression::Name("qux".to_string())),
                    ],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo(bar1=bar2, **baz, **qux)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![
                        Argument::Keyword("bar1".to_string(), Expression::Name("bar2".to_string())),
                        Argument::Kwargs(Expression::Name("baz".to_string())),
                        Argument::Kwargs(Expression::Name("qux".to_string())),
                    ],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo(bar1=bar2, **baz, qux1=qux2)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Call(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![
                        Argument::Keyword("bar1".to_string(), Expression::Name("bar2".to_string())),
                        Argument::Kwargs(Expression::Name("baz".to_string())),
                        Argument::Keyword("qux1".to_string(), Expression::Name("qux2".to_string())),
                    ],
                )),
            )),
        );
    }

    #[test]
    fn test_call_keyword_expr() {
        // The Grammar technically allows this, but CPython refuses it for good reasons;
        // let's do the same.
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(
            atom_expr(make_strspan("foo(bar1 if baz else bar2=baz)")),
            Ok((
                make_strspan("(bar1 if baz else bar2=baz)"),
                Box::new(Expression::Name("foo".to_string())),
            )),
        );
    }

    #[test]
    fn test_subscript_simple() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(
            atom_expr(make_strspan("foo[bar]")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Subscript(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Subscript::Simple(Expression::Name("bar".to_string()))],
                )),
            )),
        );
    }

    #[test]
    fn test_subscript_double() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(
            atom_expr(make_strspan("foo[bar:baz]")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Subscript(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Subscript::Double(
                        Some(Expression::Name("bar".to_string())),
                        Some(Expression::Name("baz".to_string())),
                    )],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo[bar:]")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Subscript(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Subscript::Double(
                        Some(Expression::Name("bar".to_string())),
                        None,
                    )],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo[:baz]")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Subscript(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Subscript::Double(
                        None,
                        Some(Expression::Name("baz".to_string())),
                    )],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo[:]")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Subscript(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Subscript::Double(None, None)],
                )),
            )),
        );
    }

    #[test]
    fn test_subscript_triple() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(
            atom_expr(make_strspan("foo[bar:baz:qux]")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Subscript(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Subscript::Triple(
                        Some(Expression::Name("bar".to_string())),
                        Some(Expression::Name("baz".to_string())),
                        Some(Expression::Name("qux".to_string())),
                    )],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo[bar::qux]")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Subscript(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Subscript::Triple(
                        Some(Expression::Name("bar".to_string())),
                        None,
                        Some(Expression::Name("qux".to_string())),
                    )],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo[bar::]")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Subscript(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Subscript::Triple(
                        Some(Expression::Name("bar".to_string())),
                        None,
                        None,
                    )],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo[:baz:qux]")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Subscript(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Subscript::Triple(
                        None,
                        Some(Expression::Name("baz".to_string())),
                        Some(Expression::Name("qux".to_string())),
                    )],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo[:baz:]")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Subscript(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Subscript::Triple(
                        None,
                        Some(Expression::Name("baz".to_string())),
                        None,
                    )],
                )),
            )),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo[::]")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Subscript(
                    Box::new(Expression::Name("foo".to_string())),
                    vec![Subscript::Triple(None, None, None)],
                )),
            )),
        );
    }

    #[test]
    fn test_attribute() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(
            atom_expr(make_strspan("foo.bar")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Attribute(
                    Box::new(Expression::Name("foo".to_string())),
                    "bar".to_string(),
                )),
            )),
        );
    }

    #[test]
    fn test_call_and_attribute() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(
            atom_expr(make_strspan("foo.bar().baz")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Attribute(
                    Box::new(Expression::Call(
                        Box::new(Expression::Attribute(
                            Box::new(Expression::Name("foo".to_string())),
                            "bar".to_string(),
                        )),
                        Vec::new(),
                    )),
                    "baz".to_string(),
                )),
            )),
        );
    }

    #[test]
    fn test_atom_expr() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        assert_parse_eq(
            atom_expr(make_strspan("foo.bar[baz]")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Subscript(
                    Box::new(Expression::Attribute(
                        Box::new(Expression::Name("foo".to_string())),
                        "bar".to_string(),
                    )),
                    vec![Subscript::Simple(Expression::Name("baz".to_string()))],
                )),
            )),
        );
    }

    #[test]
    fn test_call_newline() {
        let atom_expr = ExpressionParser::<NewlinesAreNotSpaces>::atom_expr;
        let ast = Box::new(Expression::Call(
            Box::new(Expression::Name("foo".to_string())),
            vec![
                Argument::Positional(Expression::Name("bar".to_string())),
                Argument::Positional(Expression::Bop(
                    Bop::Add,
                    Box::new(Expression::Name("baz".to_string())),
                    Box::new(Expression::Name("qux".to_string())),
                )),
            ],
        ));

        assert_parse_eq(
            atom_expr(make_strspan("foo(bar, baz + qux)")),
            Ok((make_strspan(""), ast.clone())),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo(bar, baz +\nqux)")),
            Ok((make_strspan(""), ast.clone())),
        );

        assert_parse_eq(
            atom_expr(make_strspan("foo(bar, baz +\n # foobar\nqux)")),
            Ok((make_strspan(""), ast)),
        );
    }

    #[test]
    fn test_setlit() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;

        assert_parse_eq(
            atom(make_strspan("{foo}")),
            Ok((
                make_strspan(""),
                Box::new(Expression::SetLiteral(vec![SetItem::Unique(
                    Expression::Name("foo".to_string()),
                )])),
            )),
        );

        assert_parse_eq(
            atom(make_strspan("{foo, bar, baz}")),
            Ok((
                make_strspan(""),
                Box::new(Expression::SetLiteral(vec![
                    SetItem::Unique(Expression::Name("foo".to_string())),
                    SetItem::Unique(Expression::Name("bar".to_string())),
                    SetItem::Unique(Expression::Name("baz".to_string())),
                ])),
            )),
        );

        assert_parse_eq(
            atom(make_strspan("{foo, *bar, baz}")),
            Ok((
                make_strspan(""),
                Box::new(Expression::SetLiteral(vec![
                    SetItem::Unique(Expression::Name("foo".to_string())),
                    SetItem::Star(Expression::Name("bar".to_string())),
                    SetItem::Unique(Expression::Name("baz".to_string())),
                ])),
            )),
        );
    }

    #[test]
    fn test_setlit_comment() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;

        assert_parse_eq(
            atom(make_strspan("{foo, \n #bar\n\n\n baz}")),
            Ok((
                make_strspan(""),
                Box::new(Expression::SetLiteral(vec![
                    SetItem::Unique(Expression::Name("foo".to_string())),
                    SetItem::Unique(Expression::Name("baz".to_string())),
                ])),
            )),
        );

        assert_parse_eq(
            atom(make_strspan("{\n #foo\n\n bar, baz}")),
            Ok((
                make_strspan(""),
                Box::new(Expression::SetLiteral(vec![
                    SetItem::Unique(Expression::Name("bar".to_string())),
                    SetItem::Unique(Expression::Name("baz".to_string())),
                ])),
            )),
        );

        assert_parse_eq(
            atom(make_strspan("{ bar, baz \n}")),
            Ok((
                make_strspan(""),
                Box::new(Expression::SetLiteral(vec![
                    SetItem::Unique(Expression::Name("bar".to_string())),
                    SetItem::Unique(Expression::Name("baz".to_string())),
                ])),
            )),
        );
    }

    #[test]
    fn test_dictlit() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;

        assert_parse_eq(
            atom(make_strspan("{}")),
            Ok((make_strspan(""), Box::new(Expression::DictLiteral(vec![])))),
        );

        assert_parse_eq(
            atom(make_strspan("{foo1:foo2}")),
            Ok((
                make_strspan(""),
                Box::new(Expression::DictLiteral(vec![DictItem::Unique(
                    Expression::Name("foo1".to_string()),
                    Expression::Name("foo2".to_string()),
                )])),
            )),
        );

        assert_parse_eq(
            atom(make_strspan("{foo1:foo2, bar1:bar2, baz1:baz2}")),
            Ok((
                make_strspan(""),
                Box::new(Expression::DictLiteral(vec![
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
                ])),
            )),
        );

        assert_parse_eq(
            atom(make_strspan("{foo1:foo2, **bar, baz1:baz2}")),
            Ok((
                make_strspan(""),
                Box::new(Expression::DictLiteral(vec![
                    DictItem::Unique(
                        Expression::Name("foo1".to_string()),
                        Expression::Name("foo2".to_string()),
                    ),
                    DictItem::Star(Expression::Name("bar".to_string())),
                    DictItem::Unique(
                        Expression::Name("baz1".to_string()),
                        Expression::Name("baz2".to_string()),
                    ),
                ])),
            )),
        );
    }

    #[test]
    fn test_comp_for() {
        let comp_for = ExpressionParser::<NewlinesAreNotSpaces>::comp_for;

        assert_parse_eq(
            comp_for(make_strspan("for bar in baz")),
            Ok((
                make_strspan(""),
                vec![ComprehensionChunk::For {
                    async: false,
                    item: vec![Expression::Name("bar".to_string())],
                    iterator: Expression::Name("baz".to_string()),
                }],
            )),
        );
    }

    #[test]
    fn test_listcomp() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;

        assert_parse_eq(
            atom(make_strspan("[foo for bar in baz]")),
            Ok((
                make_strspan(""),
                Box::new(Expression::ListComp(
                    Box::new(SetItem::Unique(Expression::Name("foo".to_string()))),
                    vec![ComprehensionChunk::For {
                        async: false,
                        item: vec![Expression::Name("bar".to_string())],
                        iterator: Expression::Name("baz".to_string()),
                    }],
                )),
            )),
        );
    }

    #[test]
    fn test_listcomp2() {
        let testlist_comp = ExpressionParser::<NewlinesAreNotSpaces>::testlist_comp;

        assert_parse_eq(
            testlist_comp(make_strspan("foo for bar in baz")),
            Ok((
                make_strspan(""),
                TestlistCompReturn::Comp(
                    Box::new(SetItem::Unique(Expression::Name("foo".to_string()))),
                    vec![ComprehensionChunk::For {
                        async: false,
                        item: vec![Expression::Name("bar".to_string())],
                        iterator: Expression::Name("baz".to_string()),
                    }],
                ),
            )),
        );
    }

    #[test]
    fn test_listcomp2_chain_for() {
        let testlist_comp = ExpressionParser::<NewlinesAreNotSpaces>::testlist_comp;

        assert_parse_eq(
            testlist_comp(make_strspan("foo for bar in baz for qux in quux")),
            Ok((
                make_strspan(""),
                TestlistCompReturn::Comp(
                    Box::new(SetItem::Unique(Expression::Name("foo".to_string()))),
                    vec![
                        ComprehensionChunk::For {
                            async: false,
                            item: vec![Expression::Name("bar".to_string())],
                            iterator: Expression::Name("baz".to_string()),
                        },
                        ComprehensionChunk::For {
                            async: false,
                            item: vec![Expression::Name("qux".to_string())],
                            iterator: Expression::Name("quux".to_string()),
                        },
                    ],
                ),
            )),
        );
    }

    #[test]
    fn test_listcomp2_chain_if() {
        let testlist_comp = ExpressionParser::<NewlinesAreNotSpaces>::testlist_comp;

        assert_parse_eq(
            testlist_comp(make_strspan("foo for bar in baz if qux")),
            Ok((
                make_strspan(""),
                TestlistCompReturn::Comp(
                    Box::new(SetItem::Unique(Expression::Name("foo".to_string()))),
                    vec![
                        ComprehensionChunk::For {
                            async: false,
                            item: vec![Expression::Name("bar".to_string())],
                            iterator: Expression::Name("baz".to_string()),
                        },
                        ComprehensionChunk::If {
                            cond: Expression::Name("qux".to_string()),
                        },
                    ],
                ),
            )),
        );
    }

    #[test]
    fn test_listcomp3() {
        let testlist_comp = ExpressionParser::<NewlinesAreNotSpaces>::testlist_comp;

        assert_parse_eq(
            testlist_comp(make_strspan("foo for (bar, baz) in qux")),
            Ok((
                make_strspan(""),
                TestlistCompReturn::Comp(
                    Box::new(SetItem::Unique(Expression::Name("foo".to_string()))),
                    vec![ComprehensionChunk::For {
                        async: false,
                        item: vec![Expression::TupleLiteral(vec![
                            SetItem::Unique(Expression::Name("bar".to_string())),
                            SetItem::Unique(Expression::Name("baz".to_string())),
                        ])],
                        iterator: Expression::Name("qux".to_string()),
                    }],
                ),
            )),
        );
    }

    #[test]
    fn test_setcomp() {
        let atom = ExpressionParser::<NewlinesAreNotSpaces>::atom;

        assert_parse_eq(
            atom(make_strspan("{foo for bar in baz}")),
            Ok((
                make_strspan(""),
                Box::new(Expression::SetComp(
                    Box::new(SetItem::Unique(Expression::Name("foo".to_string()))),
                    vec![ComprehensionChunk::For {
                        async: false,
                        item: vec![Expression::Name("bar".to_string())],
                        iterator: Expression::Name("baz".to_string()),
                    }],
                )),
            )),
        );
    }

    #[test]
    fn test_op() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;
        assert_parse_eq(
            test(make_strspan("n >= 0")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::Geq,
                    Box::new(Expression::Name("n".to_string())),
                    Box::new(Expression::Int(0u32.into())),
                )),
            )),
        );
    }

    #[test]
    fn test_lambda() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;

        assert_parse_eq(
            test(make_strspan("lambda: foo")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Lambdef(
                    Default::default(),
                    Box::new(Expression::Name("foo".to_string())),
                )),
            )),
        );

        assert_parse_eq(
            test(make_strspan("lambda : foo")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Lambdef(
                    Default::default(),
                    Box::new(Expression::Name("foo".to_string())),
                )),
            )),
        );

        assert_parse_eq(
            test(make_strspan("lambda :foo")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Lambdef(
                    Default::default(),
                    Box::new(Expression::Name("foo".to_string())),
                )),
            )),
        );
    }

    #[test]
    fn test_namedexpr() {
        let namedexpr_test = ExpressionParser::<NewlinesAreNotSpaces>::namedexpr_test;

        assert_parse_eq(
            namedexpr_test(make_strspan("foo := bar")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Named(
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Name("bar".to_string())),
                )),
            )),
        );

        assert_parse_eq(
            namedexpr_test(make_strspan("foo := (bar := baz)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Named(
                    Box::new(Expression::Name("foo".to_string())),
                    Box::new(Expression::Named(
                        Box::new(Expression::Name("bar".to_string())),
                        Box::new(Expression::Name("baz".to_string())),
                    )),
                )),
            )),
        );
    }

    #[test]
    fn test_multibop() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;

        assert_parse_eq(
            test(make_strspan("a <= b < c")),
            Ok((
                make_strspan(""),
                Box::new(Expression::MultiBop(
                    Box::new(Expression::Name("a".to_string())),
                    vec![
                        (Bop::Leq, Expression::Name("b".to_string())),
                        (Bop::Lt, Expression::Name("c".to_string())),
                    ],
                )),
            )),
        );
    }

    #[test]
    fn test_escaped_newline() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;

        assert_parse_eq(
            test(make_strspan("a <= \\\nb")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Bop(
                    Bop::Leq,
                    Box::new(Expression::Name("a".to_string())),
                    Box::new(Expression::Name("b".to_string())),
                )),
            )),
        );
    }

    #[test]
    fn test_yield() {
        let test = ExpressionParser::<NewlinesAreNotSpaces>::test;

        assert_parse_eq(
            test(make_strspan("lambda: (yield)")),
            Ok((
                make_strspan(""),
                Box::new(Expression::Lambdef(
                    Default::default(),
                    Box::new(Expression::Yield(Vec::new())),
                )),
            )),
        );
    }

    #[test]
    fn test_unpack() {
        let testlist_star_expr = ExpressionParser::<NewlinesAreNotSpaces>::testlist_star_expr;
        assert_parse_eq(
            testlist_star_expr(make_strspan("foo,")),
            Ok((
                make_strspan(""),
                vec![Expression::TupleLiteral(vec![SetItem::Unique(
                    Expression::Name("foo".to_string()),
                )])],
            )),
        );
    }
}
