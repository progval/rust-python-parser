#[macro_use]
extern crate nom;
use nom::types::CompleteStr;

#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

#[macro_use]
mod helpers;
#[macro_use]
mod statements;

use helpers::*;
use statements::*;

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

named!(pub parse_single_input <CompleteStr, Option<Statement>>,
  alt!(
    newline => { |_| None }
  | call!(statement, 0, 0) => { |stmt| Some(stmt) }
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
    fn foo() {
        assert_eq!(newline(CS("\n")), Ok((CS(""), ())));
        assert_eq!(parse_single_input(CS("del foo")), Ok((CS(""), Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])])))));
        assert_eq!(parse_single_input(CS("del foo bar")), Ok((CS(""), Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string(), "bar".to_string()])])))));
        assert_eq!(parse_single_input(CS("del foo; del bar")), Ok((CS(""), Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()]), SmallStatement::Del(vec!["bar".to_string()])])))));
        assert_eq!(parse_single_input(CS("del foo ;del bar")), Ok((CS(""), Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()]), SmallStatement::Del(vec!["bar".to_string()])])))));
    }

    #[test]
    fn test_atom() {
        assert_eq!(atom(CS("foo ")), Ok((CS(" "), Atom::Name("foo".to_string()))));
        assert_eq!(atom(CS(r#""foo" "#)), Ok((CS(" "), Atom::String("foo".to_string()))));
        assert_eq!(atom(CS(r#""fo\"o" "#)), Ok((CS(" "), Atom::String("fo\"o".to_string()))));
        assert_eq!(atom(CS(r#""fo"o" "#)), Ok((CS(r#"o" "#), Atom::String("fo".to_string()))));
    }
}
