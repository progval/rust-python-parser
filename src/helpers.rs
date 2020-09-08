#[cfg(test)]
use std::fmt::Debug;

use unicode_xid::UnicodeXID;

use nom::types::CompleteStr;
use nom::Slice;
use nom_locate::LocatedSpan;
pub(crate) type StrSpan<'a> = LocatedSpan<CompleteStr<'a>>;

/// Like `ws!()`, but does not allow newlines.
macro_rules! ws_nonl (
  ($i:expr, $($args:tt)*) => (
    {
      use nom::Convert;
      use nom::Err;

      match sep!($i, $crate::helpers::spaces_nonl, $($args)*) {
        Err(e) => Err(e),
        Ok((i1,o))    => {
          match $crate::helpers::spaces_nonl(i1) {
            Err(e) => Err(Err::convert(e)),
            Ok((i2,_))    => Ok((i2, o))
          }
        }
      }
    }
  )
);

/// Like `ws!()`, but ignores comments as well
macro_rules! ws_comm (
  ($i:expr, $($args:tt)*) => (
    {
      use nom::Convert;
      use nom::Err;

      match sep!($i, $crate::helpers::spaces_nl, $($args)*) {
        Err(e) => Err(e),
        Ok((i1,o))    => {
          match $crate::helpers::spaces_nl(i1) {
            Err(e) => Err(Err::convert(e)),
            Ok((i2,_))    => Ok((i2, o))
          }
        }
      }
    }
  )
);

named!(escaped_newline<StrSpan, ()>,
  map!(terminated!(char!('\\'), char!('\n')), |_| ())
);

named!(pub spaces_nl<StrSpan, ()>,
  map!(many0!(alt!(one_of!(" \t\x0c") => { |_|() } | escaped_newline | newline)), |_| ())
);

// Bottleneck:
// named!(pub spaces_nonl<StrSpan, ()>,
//   map!(many0!(alt!(one_of!(" \t\x0c") => { |_| () }|escaped_newline)), |_| ())
// );
// Rewritten as:
pub fn spaces_nonl(i: StrSpan) -> Result<(StrSpan, ()), ::nom::Err<StrSpan>> {
    let mut it = i.fragment.chars().enumerate().peekable();
    while let Some((index, c)) = it.next() {
        let next_char = it.peek().map(|&(_, c)| c);
        match c {
            ' ' | '\t' | '\x0c' => (),
            '\\' if next_char.unwrap_or(' ') == '\n' => {
                it.next();
            }
            _ => {
                if index == 0 {
                    return Ok((i, ()));
                } else {
                    return Ok((i.slice(index..), ()));
                }
            }
        }
    }
    Ok((i.slice(i.fragment.len()..), ()))
}

named!(pub space_sep_nl<StrSpan, ()>,
  map!(many1!(alt!(one_of!(" \t\x0c") => { |_|() } | escaped_newline | newline)), |_| ())
);

named!(pub space_sep_nonl<StrSpan, ()>,
  map!(many1!(alt!(one_of!(" \t\x0c") => { |_| () } | escaped_newline)), |_| ())
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
pub(crate) trait AreNewlinesSpaces {
    const VALUE: bool;
}
pub(crate) struct NewlinesAreSpaces;
impl AreNewlinesSpaces for NewlinesAreSpaces {
    const VALUE: bool = true;
}
pub(crate) struct NewlinesAreNotSpaces;
impl AreNewlinesSpaces for NewlinesAreNotSpaces {
    const VALUE: bool = false;
}

macro_rules! spaces {
    ( $i:expr, $($args:tt)* ) => {
        match ANS::VALUE {
            true => call!($i, $crate::helpers::spaces_nl, $($args)*),
            false => call!($i, $crate::helpers::spaces_nonl, $($args)*),
        }
    }
}

macro_rules! ws_auto {
    ( $i:expr, $($args:tt)* ) => {
        delimited!($i, spaces!(), $($args)*, spaces!())
    }
}

macro_rules! space_sep {
    ( $i:expr, $($args:tt)* ) => {
        match ANS::VALUE {
            true => call!($i, $crate::helpers::space_sep_nl, $($args)*),
            false => call!($i, $crate::helpers::space_sep_nonl, $($args)*),
        }
    }
}

const KEYWORDS: [&'static str; 2] = ["yield", "import"];
named!(pub name<StrSpan, String>,
  do_parse!(
    name: map!(
      tuple!(
        alt!(char!('_') | verify!(call!(::nom::anychar), |c| UnicodeXID::is_xid_start(c))),
        take_while!(call!(|c| UnicodeXID::is_xid_continue(c)))
      ), |(c, s)| format!("{}{}", c, s.fragment)
    ) >>
    verify!(tag!(""), |_| !KEYWORDS.contains(&&name[..])) >>
    (name)
  )
);

named!(pub word_end<StrSpan, ()>,
  not!(verify!(peek!(::nom::anychar), |c| UnicodeXID::is_xid_continue(c)))
);

macro_rules! keyword {
    ($i:expr, $kw:expr) => {
        terminated!($i, tag!($kw), word_end)
    };
}

named!(pub newline<StrSpan, ()>,
  map!(
    many1!(
      tuple!(
        spaces_nonl,
        opt!(preceded!(char!('#'), many0!(none_of!("\n")))),
        char!('\n')
      )
    ),
    |_| ()
  )
);

named!(pub semicolon<StrSpan, ()>,
  map!(ws_nonl!(char!(';')), |_| ())
);

/// Helper to make an instance of `StrSpan`, that can be used as the argument
/// to other parsers.
pub fn make_strspan(s: &str) -> StrSpan {
    StrSpan::new(CompleteStr(s))
}

#[cfg(test)]
pub(crate) fn assert_parse_eq<T: Debug + PartialEq>(
    left: Result<(StrSpan, T), ::nom::Err<StrSpan>>,
    right: Result<(StrSpan, T), ::nom::Err<StrSpan>>,
) {
    use nom::Context;
    match (left, right) {
        (Ok((left_span, left_tree)), Ok((right_span, right_tree))) => assert_eq!(
            ((left_span.fragment, left_tree)),
            ((right_span.fragment, right_tree))
        ),
        (
            Err(::nom::Err::Failure(Context::Code(left_span, left_code))),
            Err(::nom::Err::Failure(Context::Code(right_span, right_code))),
        ) => assert_eq!(
            (left_span.fragment, left_code),
            (right_span.fragment, right_code)
        ),
        (Err(::nom::Err::Incomplete(_)), _) => unreachable!(),
        (_, Err(::nom::Err::Incomplete(_))) => panic!("We're only using complete strings here!"),
        (l, r) => assert_eq!(l, r),
    }
}

pub(crate) fn first_word(i: StrSpan) -> Result<(StrSpan, &str), ::nom::Err<StrSpan>> {
    map!(i, terminated!(call!(::nom::alpha), word_end), |s| s
        .fragment
        .0)
}

// https://github.com/Geal/nom/pull/800
macro_rules! fold_many1_fixed(
  ($i:expr, $submac:ident!( $($args:tt)* ), $init:expr, $f:expr) => (
    {
      use nom;
      use nom::lib::std::result::Result::*;
      use nom::{Err,Needed,InputLength,Context,AtEof};

      match $submac!($i, $($args)*) {
        Err(Err::Error(_))      => Err(Err::Error(
          error_position!($i, nom::ErrorKind::Many1)
        )),
        Err(Err::Failure(_))      => Err(Err::Failure(
          error_position!($i, nom::ErrorKind::Many1)
        )),
        Err(Err::Incomplete(i)) => Err(Err::Incomplete(i)),
        Ok((i1,o1))   => {
          let f = $f;
          let mut acc = f($init, o1);
          let mut input  = i1;
          let mut incomplete: nom::lib::std::option::Option<Needed> =
            nom::lib::std::option::Option::None;
          let mut failure: nom::lib::std::option::Option<Context<_,_>> =
            nom::lib::std::option::Option::None;
          loop {
            match $submac!(input, $($args)*) {
              Err(Err::Error(_))                    => {
                break;
              },
              Err(Err::Incomplete(i)) => {
                incomplete = nom::lib::std::option::Option::Some(i);
                break;
              },
              Err(Err::Failure(e)) => {
                failure = nom::lib::std::option::Option::Some(e);
                break;
              },
              Ok((i, o)) => {
                if i.input_len() == input.input_len() {
                  if !i.at_eof() {
                    failure = nom::lib::std::option::Option::Some(error_position!(i, nom::ErrorKind::Many1));
                  }
                  break;
                }
                acc = f(acc, o);
                input = i;
              }
            }
          }

          match failure {
            nom::lib::std::option::Option::Some(e) => Err(Err::Failure(e)),
            nom::lib::std::option::Option::None    => match incomplete {
              nom::lib::std::option::Option::Some(i) => nom::need_more($i, i),
              nom::lib::std::option::Option::None    => Ok((input, acc))
            }
          }
        }
      }
    }
  );
  ($i:expr, $f:expr, $init:expr, $fold_f:expr) => (
    fold_many_fixed1!($i, call!($f), $init, $fold_f);
  );
);

macro_rules! indent {
    ($i:expr, $nb_spaces:expr) => {{
        use nom::ErrorKind;
        use $crate::errors::PyParseError;
        count!($i, char!(' '), $nb_spaces).and_then(|(i2, _)| {
            return_error!(
                i2,
                ErrorKind::Custom(PyParseError::UnexpectedIndent.into()),
                not!(peek!(char!(' ')))
            )
        })
    }};
}
