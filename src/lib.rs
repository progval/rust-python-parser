#[macro_use]
extern crate nom;
use nom::alpha;

#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

pub type Atom<'a> = &'a str;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SmallStatement<'a> {
    Del(Vec<Atom<'a>>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SingleInput<'a> {
    None,
    SimpleStatement(Vec<SmallStatement<'a>>),
    //CompoundStatement(CompoundStatement),
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

named!(pub parse_single_input<&str, SingleInput>,
  do_parse!(
  foo: alt!(
    newline => { |_| SingleInput::None } |
    simple_stmt => { |stmt| SingleInput::SimpleStatement(stmt) }
    //map!(tuple!(simple_stmt, newline), |(stmt, _)| SingleInput::CompoundStatement(stmt))
  ) >>
  ( foo )
)
);

named!(simple_stmt<&str, Vec<SmallStatement>>,
  do_parse!(
    first_stmts: many0!(terminated!(small_stmt, char!(';'))) >>
    last_stmt: small_stmt >>
    opt!(char!(';')) >>
    newline >> ({
      let mut stmts = first_stmts;
      stmts.push(last_stmt);
      stmts
    })
  )
);

named!(small_stmt<&str, SmallStatement>,
  alt!(
    del_stmt => { |atoms| SmallStatement::Del(atoms) }
    // TODO
  )
);

named!(del_stmt<&str, Vec<Atom>>,
  preceded!(tag!("del "), ws2!(many1!(atom)))
  // TODO
);

named!(atom<&str, Atom>,
  alt!(alpha)
  // TODO
);

named!(newline<&str, ()>,
  map!(char!('\n'), |_| ())
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn foo() {
        assert_eq!(newline("\n"), Ok(("", ())));
        assert_eq!(atom("foo "), Ok((" ", "foo")));
        assert_eq!(del_stmt("del foo\n"), Ok(("\n", vec!["foo"])));
        assert_eq!(parse_single_input("del foo\n"), Ok(("", SingleInput::SimpleStatement(vec![SmallStatement::Del(vec!["foo"])]))));
    }
}
