#[macro_use]
extern crate nom;
use nom::alpha;

#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

pub type Name = String;

pub type Test = String;

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

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SmallStatement {
    // TODO
    Del(Vec<Name>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Statement {
    Simple(Vec<SmallStatement>),
    Compound(Box<CompoundStatement>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CompoundStatement {
    // TODO
    If(Vec<(Test, Vec<Statement>)>, Option<Statement>),
}

named!(pub space<&str, &str>, eat_separator!(&b" \t"[..]));

#[macro_export]
macro_rules! ws2 (
  ($i:expr, $($args:tt)*) => (
    {
      use nom::Convert;
      use nom::Err;

      match sep!($i, space, $($args)*) {
        Err(e) => Err(e),
        Ok((i1,o))    => {
          match space(i1) {
            Err(e) => Err(Err::convert(e)),
            Ok((i2,_))    => Ok((i2, o))
          }
        }
      }
    }
  )
);

named!(pub parse_single_input <&str, Option<Statement>>,
  alt!(
    newline => { |_| None }
  | call!(statement, 0, 0) => { |stmt| Some(stmt) }
  )
);

named_args!(statement(first_indent: usize, indent: usize) <&str, Statement>,
  alt!(
    call!(simple_stmt, first_indent) => { |stmts| Statement::Simple(stmts) }
  | terminated!(call!(compound_stmt, first_indent, indent), ws!(newline)) => { |stmt| Statement::Compound(Box::new(stmt)) }
  )
);

named_args!(simple_stmt(indent: usize) <&str, Vec<SmallStatement>>,
  do_parse!(
    count!(char!(' '), indent) >>
    first_stmts: many0!(terminated!(call!(small_stmt), ws2!(semicolon))) >>
    last_stmt: small_stmt >>
    opt!(ws2!(semicolon)) >>
    newline >> ({
      let mut stmts = first_stmts;
      stmts.push(last_stmt);
      stmts
    })
  )
);

named_args!(block(indent: usize) <&str, Vec<Statement>>,
  do_parse!(
    new_indent: do_parse!(
      count!(char!(' '), indent) >>
      new_spaces: many1!(char!(' ')) >> (
        indent + new_spaces.len()
      )
    ) >>
    stmt: many1!(call!(statement, 0, new_indent)) >> (
      stmt
    )
  )
);



named_args!(compound_stmt(first_indent: usize, indent: usize) <&str, CompoundStatement>,
  do_parse!(
    count!(char!(' '), first_indent) >>
    content: alt!(
      tuple!(
        tag!("if "), ws2!(tag!("foo")), char!(':'), newline,
        call!(block, indent)
      ) => { |(_, foo, _, _, block): (_, &str, _, _, _)| CompoundStatement::If(vec![(foo.to_string(), block)], None)}
    ) >> (
      content
    )
  )
);

named!(small_stmt<&str, SmallStatement>,
  alt!(
    del_stmt => { |atoms| SmallStatement::Del(atoms) }
    // TODO
  )
);

named!(del_stmt<&str, Vec<String>>,
  preceded!(tag!("del "), ws2!(many1!(name)))
  // TODO
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

named!(name<&str, String>,
  map!(alpha, |s| s.to_string())
  // TODO
);

named!(newline<&str, ()>,
  map!(preceded!(space, char!('\n')), |_| ())
);

named!(semicolon<&str, ()>,
  map!(ws2!(char!(';')), |_| ())
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn foo() {
        assert_eq!(newline("\n"), Ok(("", ())));
        assert_eq!(del_stmt("del foo\n"), Ok(("\n", vec!["foo".to_string()])));
        assert_eq!(parse_single_input("del foo\n"), Ok(("", Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])])))));
        assert_eq!(parse_single_input("del foo bar\n"), Ok(("", Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string(), "bar".to_string()])])))));
        assert_eq!(parse_single_input("del foo; del bar\n"), Ok(("", Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()]), SmallStatement::Del(vec!["bar".to_string()])])))));
        assert_eq!(parse_single_input("del foo ;del bar\n"), Ok(("", Some(Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()]), SmallStatement::Del(vec!["bar".to_string()])])))));
    }

    #[test]
    fn test_statement_indent() {
        assert_eq!(statement("del foo\n", 0, 0), Ok(("", Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])]))));
        assert_eq!(statement(" del foo\n", 1, 1), Ok(("", Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])]))));
        assert!(statement("del foo\n", 1, 1).is_err());
        assert!(statement(" del foo\n", 0, 0).is_err());
    }

    #[test]
    fn test_block() {
        assert_eq!(block(" del foo\n\n", 0), Ok(("\n", vec![Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])])])));
        assert_eq!(block("  del foo\n\n", 1), Ok(("\n", vec![Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])])])));
        assert_eq!(block("      del foo\n\n", 1), Ok(("\n", vec![Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])])])));
        assert!(block("del foo\n\n", 0).is_err());
        assert!(block("del foo\n\n", 1).is_err());
        assert!(block(" del foo\n\n", 1).is_err());
    }

    #[test]
    fn test_atom() {
        assert_eq!(atom("foo "), Ok((" ", Atom::Name("foo".to_string()))));
        assert_eq!(atom(r#""foo" "#), Ok((" ", Atom::String("foo".to_string()))));
        assert_eq!(atom(r#""fo\"o" "#), Ok((" ", Atom::String("fo\"o".to_string()))));
        assert_eq!(atom(r#""fo"o" "#), Ok((r#"o" "#, Atom::String("fo".to_string()))));
    }

    #[test]
    fn test_if() {
        assert_eq!(compound_stmt("if foo:\n del bar\n ", 0, 0), Ok((" ",
            CompoundStatement::If(
                vec![("foo".to_string(),
                    vec![
                        Statement::Simple(vec![
                            SmallStatement::Del(vec!["bar".to_string()])
                        ])
                    ]
                )],
                None
            )
        )));
    }
}
