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

use helpers::*;
use expressions::*;
use statements::*;

named!(pub parse_single_input <CompleteStr, Option<Statement>>,
  alt!(
    newline => { |_| None }
  | call!(statement, 0, 0) => { |stmt| Some(stmt) }
  )
);

#[cfg(test)]
mod tests {
    use super::*;
    use nom::types::CompleteStr as CS;

    #[test]
    fn foo() {
        assert_eq!(newline(CS("\n")), Ok((CS(""), ())));
        assert_eq!(parse_single_input(CS("del foo")), Ok((CS(""), Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])])))));
        assert_eq!(parse_single_input(CS("del foo bar")), Ok((CS(""), Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string(), "bar".to_string()])])))));
        assert_eq!(parse_single_input(CS("del foo; del bar")), Ok((CS(""), Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()]), SmallStatement::Del(vec!["bar".to_string()])])))));
        assert_eq!(parse_single_input(CS("del foo ;del bar")), Ok((CS(""), Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()]), SmallStatement::Del(vec!["bar".to_string()])])))));
    }
}
