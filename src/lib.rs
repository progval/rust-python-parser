//! A Python parser based on nom, plus some utilities.
//!
//! # Panics
//!
//! Never (except stack overflows).
//!
//! # Numbers
//!
//! Python's integer literals may be arbitrary large. This is supported
//! thanks to the `num_bigint` crate.
//! Disable the `bigint` feature to fall back to `u64`.
//!
//! # String encoding
//!
//! `ast::PyString`s are WTF8-encoded if the `wtf8` feature is enabled
//! (the default) allowing full support for Python's string litteral.
//!
//! If that feature is disabled, they default to regular Rust string
//! Note that without the `wtf8` feature, some valid string
//! literals will be badly parsed (missing characters).
//!
//! # Example
//!
//! ```
//! extern crate python_parser;
//! use python_parser::ast::*;
//! let code = "print(2 + 3, fd=sys.stderr)";
//! let ast = python_parser::file_input(python_parser::make_strspan(code))
//!           .unwrap()
//!           .1;
//! assert_eq!(ast,
//!     vec![
//!         Statement::Assignment(
//!             vec![
//!                 Expression::Call(
//!                     Box::new(Expression::Name("print".to_string())),
//!                     vec![
//!                         Argument::Positional(
//!                             Expression::Bop(
//!                                 Bop::Add,
//!                                 Box::new(Expression::Int(2u32.into())),
//!                                 Box::new(Expression::Int(3u32.into())),
//!                             )
//!                         ),
//!                         Argument::Keyword(
//!                             "fd".to_string(),
//!                             Expression::Attribute(
//!                                 Box::new(Expression::Name("sys".to_string())),
//!                                 "stderr".to_string(),
//!                             )
//!                         ),
//!                     ]
//!                 ),
//!             ],
//!             vec![],
//!         )
//!     ]
//! );
//! ```

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
named_attr!(#[doc = "Parses a single interactive statement, like in the REPL."],
pub parse_single_input <StrSpan, Vec<Statement>>,
  alt!(
    newline => { |_| Vec::new() }
  | call!(statement, 0) => { |stmts| stmts }
  )
);

// file_input: (NEWLINE | stmt)* ENDMARKER
named_attr!(#[doc = "Parses a module or sequence of commands."],
pub file_input <StrSpan, Vec<Statement>>,
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
named_attr!(#[doc = "Parses the input of eval()."],
pub eval_input <StrSpan, Vec<Expression>>,
  terminated!(ws_nonl!(call!(ExpressionParser::<NewlinesAreNotSpaces>::testlist)), many0!(newline))
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
