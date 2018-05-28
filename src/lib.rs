#[macro_use]
extern crate nom;

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

named!(pub parse_single_input <&str, Option<Statement>>,
  alt!(
    newline => { |_| None }
  | call!(statement, 0, 0) => { |stmt| Some(stmt) }
  )
);

use nom::Needed; // Required by escaped_transform, see https://github.com/Geal/nom/issues/780
named!(atom<&str, Atom>,
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

    #[test]
    fn foo() {
        assert_eq!(newline("\n"), Ok(("", ())));
        assert_eq!(parse_single_input("del foo\n"), Ok(("", Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])])))));
        assert_eq!(parse_single_input("del foo bar\n"), Ok(("", Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string(), "bar".to_string()])])))));
        assert_eq!(parse_single_input("del foo; del bar\n"), Ok(("", Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()]), SmallStatement::Del(vec!["bar".to_string()])])))));
        assert_eq!(parse_single_input("del foo ;del bar\n"), Ok(("", Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()]), SmallStatement::Del(vec!["bar".to_string()])])))));
    }

    #[test]
    fn test_atom() {
        assert_eq!(atom("foo "), Ok((" ", Atom::Name("foo".to_string()))));
        assert_eq!(atom(r#""foo" "#), Ok((" ", Atom::String("foo".to_string()))));
        assert_eq!(atom(r#""fo\"o" "#), Ok((" ", Atom::String("fo\"o".to_string()))));
        assert_eq!(atom(r#""fo"o" "#), Ok((r#"o" "#, Atom::String("fo".to_string()))));
    }
}
