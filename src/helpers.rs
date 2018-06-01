use nom::types::CompleteStr;

named!(pub space<CompleteStr, CompleteStr>, eat_separator!(&b" \t"[..]));

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

named!(pub space_sep<CompleteStr, ()>,
  map!(many1!(one_of!(" \t\n")), |_| ())
);

named!(pub space_sep2<CompleteStr, ()>,
  map!(many1!(one_of!(" \t")), |_| ())
);

pub type Name = String;

pub type Test = String;

pub type Expr = String;

use nom::alphanumeric;
named!(pub name<CompleteStr, String>,
  map!(alphanumeric, |s| s.to_string())
  // TODO
);

named!(pub newline<CompleteStr, ()>,
  map!(preceded!(space, char!('\n')), |_| ())
);

named!(pub semicolon<CompleteStr, ()>,
  map!(ws2!(char!(';')), |_| ())
);
