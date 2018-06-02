#![recursion_limit="128"]

#[macro_use]
extern crate nom;
use nom::types::CompleteStr;

#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

#[macro_use]
mod helpers;
#[macro_use]
mod expressions;
#[macro_use]
mod statements;
mod functions;

use helpers::*;
use statements::*;
use expressions::*;

// single_input: NEWLINE | simple_stmt | compound_stmt NEWLINE
named!(pub parse_single_input <CompleteStr, Vec<Statement>>,
  alt!(
    newline => { |_| Vec::new() }
  | call!(statement, 0, 0) => { |stmts| stmts }
  )
);

// file_input: (NEWLINE | stmt)* ENDMARKER
named!(pub file_input <CompleteStr, Vec<Statement>>,
  fold_many0!(
    alt!(
      call!(statement, 0, 0) => { |s| Some(s) }
    | newline => { |_| None }
    ),
    Vec::new(),
    |acc: Vec<_>, item| { let mut acc = acc; if let Some(s) = item { acc.extend(s); } acc }
  )
);

// eval_input: testlist NEWLINE* ENDMARKER
named!(pub eval_input <CompleteStr, Vec<Expression>>,
  terminated!(ws2!(call!(ExpressionParser::<NewlinesAreNotSpaces>::testlist)), many0!(newline))
);

// encoding_decl: NAME
// TODO

#[cfg(test)]
mod tests {
    use super::*;
    use nom::types::CompleteStr as CS;

    #[test]
    fn foo() {
        assert_eq!(newline(CS("\n")), Ok((CS(""), ())));
        assert_eq!(parse_single_input(CS("del foo")), Ok((CS(""), vec![Statement::Del(vec!["foo".to_string()])])));
        assert_eq!(parse_single_input(CS("del foo bar")), Ok((CS(""), vec![Statement::Del(vec!["foo".to_string(), "bar".to_string()])])));
        assert_eq!(parse_single_input(CS("del foo; del bar")), Ok((CS(""), vec![Statement::Del(vec!["foo".to_string()]), Statement::Del(vec!["bar".to_string()])])));
        assert_eq!(parse_single_input(CS("del foo ;del bar")), Ok((CS(""), vec![Statement::Del(vec!["foo".to_string()]), Statement::Del(vec!["bar".to_string()])])));
    }
}
