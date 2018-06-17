#![recursion_limit="128"]

#[macro_use]
extern crate nom;
extern crate nom_locate;

#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

extern crate unicode_xid;
extern crate unicode_names2;

#[cfg(feature="bigint")]
extern crate num_traits;
#[cfg(feature="bigint")]
extern crate num_bigint;

#[cfg(feature="wtf8")]
extern crate wtf8;

#[macro_use]
mod helpers;
#[macro_use]
mod expressions;
#[macro_use]
mod statements;
mod functions;
mod strings;
mod bytes;
mod numbers;
pub mod ast;
pub mod visitors;

use helpers::*;
use statements::*;
use expressions::*;
use ast::*;

pub use helpers::make_strspan;

// single_input: NEWLINE | simple_stmt | compound_stmt NEWLINE
named!(pub parse_single_input <StrSpan, Vec<Statement>>,
  alt!(
    newline => { |_| Vec::new() }
  | call!(statement, 0) => { |stmts| stmts }
  )
);

// file_input: (NEWLINE | stmt)* ENDMARKER
named!(pub file_input <StrSpan, Vec<Statement>>,
  fold_many0!(
    alt!(
      call!(statement, 0) => { |s| Some(s) }
    | newline => { |_| None }
    ),
    Vec::new(),
    |acc: Vec<_>, item| { let mut acc = acc; if let Some(s) = item { acc.extend(s); } acc }
  )
);

// eval_input: testlist NEWLINE* ENDMARKER
named!(pub eval_input <StrSpan, Vec<Expression>>,
  terminated!(ws2!(call!(ExpressionParser::<NewlinesAreNotSpaces>::testlist)), many0!(newline))
);

// encoding_decl: NAME
// TODO

#[cfg(test)]
mod tests {
    use super::*;
    use helpers::{make_strspan, assert_parse_eq};

    #[test]
    fn foo() {
        assert_parse_eq(newline(make_strspan("\n")), Ok((make_strspan(""), ())));
        assert_parse_eq(parse_single_input(make_strspan("del foo")), Ok((make_strspan(""), vec![Statement::Del(vec![Expression::Name("foo".to_string())])])));
        assert_parse_eq(parse_single_input(make_strspan("del foo, bar")), Ok((make_strspan(""), vec![Statement::Del(vec![Expression::Name("foo".to_string()), Expression::Name("bar".to_string())])])));
        assert_parse_eq(parse_single_input(make_strspan("del foo; del bar")), Ok((make_strspan(""), vec![Statement::Del(vec![Expression::Name("foo".to_string())]), Statement::Del(vec![Expression::Name("bar".to_string())])])));
        assert_parse_eq(parse_single_input(make_strspan("del foo ;del bar")), Ok((make_strspan(""), vec![Statement::Del(vec![Expression::Name("foo".to_string())]), Statement::Del(vec![Expression::Name("bar".to_string())])])));
    }
}
