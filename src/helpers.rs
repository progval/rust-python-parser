#[cfg(test)]
use std::fmt::Debug;

use nom::types::CompleteStr;
use nom_locate::LocatedSpan;
pub(crate) type StrSpan<'a> = LocatedSpan<CompleteStr<'a>>;

named!(pub space<StrSpan, StrSpan>, eat_separator!(&b" \t"[..]));

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

named!(pub spaces<StrSpan, ()>,
  map!(many0!(one_of!(" \t\n")), |_| ())
);

named!(pub spaces2<StrSpan, ()>,
  map!(many0!(one_of!(" \t")), |_| ())
);

named!(pub space_sep<StrSpan, ()>,
  map!(many1!(one_of!(" \t\n")), |_| ())
);

named!(pub space_sep2<StrSpan, ()>,
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

use nom::alphanumeric;
named!(pub name<StrSpan, String>,
  map!(alphanumeric, |s| s.to_string())
  // TODO
);

named!(pub newline<StrSpan, ()>,
  map!(preceded!(space, char!('\n')), |_| ())
);

named!(pub semicolon<StrSpan, ()>,
  map!(ws2!(char!(';')), |_| ())
);

#[cfg(test)]
pub(crate) fn make_strspan(s: &str) -> StrSpan {
    StrSpan::new(CompleteStr(s))
}

#[cfg(test)]
pub(crate) fn assert_parse_eq<T: Debug + PartialEq>(
        left:  Result<(StrSpan, T), ::nom::Err<StrSpan>>,
        right: Result<(StrSpan, T), ::nom::Err<StrSpan>>,
        ) {
    use nom::Context;
    match (left, right) {
        (Ok((left_span, left_tree)), Ok((right_span, right_tree))) =>
            assert_eq!(((left_span.fragment, left_tree)), ((right_span.fragment, right_tree))),
        (Err(::nom::Err::Failure(Context::Code(left_span, left_code))), Err(::nom::Err::Failure(Context::Code(right_span, right_code)))) =>
            assert_eq!((left_span.fragment, left_code), (right_span.fragment, right_code)),
        (Err(::nom::Err::Incomplete(_)), _) => unreachable!(),
        (_, Err(::nom::Err::Incomplete(_))) => panic!("We're only using complete strings here!"),
        (l, r) => assert_eq!(l, r),
    }
}
