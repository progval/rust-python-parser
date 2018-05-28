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


pub type Name = String;

pub type Test = String;

use nom::alpha;
named!(pub name<&str, String>,
  map!(alpha, |s| s.to_string())
  // TODO
);

named!(pub newline<&str, ()>,
  map!(preceded!(space, char!('\n')), |_| ())
);

named!(pub semicolon<&str, ()>,
  map!(ws2!(char!(';')), |_| ())
);
