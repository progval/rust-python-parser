use nom::types::CompleteStr;

named!(pub space<CompleteStr, CompleteStr>, eat_separator!(&b" \t"[..]));

#[macro_export]
macro_rules! ws2 (
  ($i:expr, $($args:tt)*) => (
    {
      use nom::Convert;
      use nom::Err;

      match sep!($i, $crate::helpers::space, $($args)*) {
        Err(e) => Err(e),
        Ok((i1,o))    => {
          match $crate::helpers::space(i1) {
            Err(e) => Err(Err::convert(e)),
            Ok((i2,_))    => Ok((i2, o))
          }
        }
      }
    }
  )
);

named!(pub spaces<CompleteStr, ()>,
  map!(many0!(one_of!(" \t\n")), |_| ())
);

named!(pub spaces2<CompleteStr, ()>,
  map!(many0!(one_of!(" \t")), |_| ())
);

named!(pub space_sep<CompleteStr, ()>,
  map!(many1!(one_of!(" \t\n")), |_| ())
);

named!(pub space_sep2<CompleteStr, ()>,
  map!(many1!(one_of!(" \t")), |_| ())
);

// Let me explain this ugliness.
//
// We allow newlines in expressions if and only if the newline is
// wrapped in parenthesis, square brackets, or curly brackets.
// As any given subparser can be used either in or out one of these
// pairs, we need either:
//
// 1. a boolean argument to the subparser telling whether it is wrapped
//    in one of these pairs or not
// 2. two versions of each subparser
//
// The first version has the downside of requiring run-time checks, whereas
// the second one resolves everything at compile-time.
//
// Since I do not want to write each subparser twice, I'm writing them
// in the impl{} of a polymorphic structure, which has a static boolean
// argument corresponding to newlines, so monomorphing the structure
// generates the two subparsers. Then, a simple constant propagation
// is able to get rid of the runtime checks for this boolean.
pub(crate) trait AreNewlinesSpaces { const VALUE: bool; }
pub(crate) struct NewlinesAreSpaces; impl AreNewlinesSpaces for NewlinesAreSpaces { const VALUE: bool = true; }
pub(crate) struct NewlinesAreNotSpaces; impl AreNewlinesSpaces for NewlinesAreNotSpaces { const VALUE: bool = false; }

macro_rules! spaces {
    ( $i:expr, $($args:tt)* ) => {
        match ANS::VALUE {
            true => call!($i, $crate::helpers::spaces, $($args)*),
            false => call!($i, $crate::helpers::spaces2, $($args)*),
        }
    }
}

macro_rules! space_sep {
    ( $i:expr, $($args:tt)* ) => {
        match ANS::VALUE {
            true => call!($i, $crate::helpers::space_sep, $($args)*),
            false => call!($i, $crate::helpers::space_sep2, $($args)*),
        }
    }
}

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
