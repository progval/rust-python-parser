use nom::anychar;

#[cfg(feature = "unicode-names")]
use unicode_names2;

#[cfg(not(feature = "unicode-names"))]
use errors::PyParseError;

#[cfg(feature = "wtf8")]
use wtf8;

use ast::*;
use helpers::StrSpan;

#[cfg(feature = "wtf8")]
fn cp_from_char(c: char) -> wtf8::CodePoint {
    wtf8::CodePoint::from_char(c)
}
#[cfg(feature = "wtf8")]
fn cp_from_u32(n: u32) -> Option<wtf8::CodePoint> {
    wtf8::CodePoint::from_u32(n)
}
#[cfg(not(feature = "wtf8"))]
fn cp_from_char(c: char) -> char {
    c
}
#[cfg(not(feature = "wtf8"))]
fn cp_from_u32(n: u32) -> Option<char> {
    ::std::char::from_u32(n)
}

#[cfg(feature = "unicode-names")]
named!(unicode_escaped_name<StrSpan, Option<PyStringCodePoint>>,
  map!(
    preceded!(char!('N'), delimited!(char!('{'), many1!(none_of!("}")), char!('}'))),
    |name: Vec<char>| unicode_names2::character(&name.iter().collect::<String>()).map(cp_from_char)
  )
);

#[cfg(not(feature = "unicode-names"))]
pub fn unicode_escaped_name(
    i: StrSpan,
) -> Result<(StrSpan, Option<PyStringCodePoint>), ::nom::Err<StrSpan>> {
    Err(::nom::Err::Error(::nom::Context::Code(
        i,
        ::nom::ErrorKind::Custom(PyParseError::DisabledFeature.into()),
    )))
}

named!(escapedchar<StrSpan, Option<PyStringCodePoint>>,
  preceded!(char!('\\'),
    alt!(
      char!('\n') => { |_| None }
    | char!('\\') => { |_| Some(cp_from_char('\\')) }
    | char!('\'') => { |_| Some(cp_from_char('\'')) }
    | char!('"') => { |_| Some(cp_from_char('"')) }
    | char!('a') => { |_| Some(cp_from_char('\x07')) } // BEL
    | char!('b') => { |_| Some(cp_from_char('\x08')) } // BS
    | char!('f') => { |_| Some(cp_from_char('\x0c')) } // FF
    | char!('n') => { |_| Some(cp_from_char('\n')) }
    | char!('r') => { |_| Some(cp_from_char('\r')) }
    | char!('t') => { |_| Some(cp_from_char('\t')) }
    | char!('v') => { |_| Some(cp_from_char('\x0b')) } // VT
    | tuple!(one_of!("01234567"), opt!(one_of!("01234567")), opt!(one_of!("01234567"))) => { |(c1, c2, c3): (char, Option<char>, Option<char>)|
        match (c1.to_digit(8), c2.and_then(|c| c.to_digit(8)), c3.and_then(|c| c.to_digit(8))) {
            (Some(d1), Some(d2), Some(d3)) => cp_from_u32((d1 << 6) + (d2 << 3) + d3),
            (Some(d1), Some(d2), None    ) => cp_from_u32((d1 << 3) + d2),
            (Some(d1), None,     None    ) => cp_from_u32(d1),
            _ => unreachable!(),
        }
      }
    | preceded!(char!('x'), tuple!(one_of!("0123456789abcdefABCDEF"), one_of!("0123456789abcdefABCDEF"))) => { |(c1, c2): (char, char)|
        match (c1.to_digit(16), c2.to_digit(16)) {
            (Some(d1), Some(d2)) => cp_from_u32((d1 << 4) + d2),
            _ => unreachable!(),
        }
      }
    | unicode_escaped_name
    | preceded!(char!('u'), count!(one_of!("0123456789abcdefABCDEF"), 4)) => { |v: Vec<char>| {
        let v: Vec<u32> = v.iter().map(|c| c.to_digit(16).unwrap()).collect();
        cp_from_u32((v[0] << 12) + (v[1] << 8) + (v[2] << 4) + v[3])
      }}
    | preceded!(char!('U'), count!(one_of!("0123456789abcdefABCDEF"), 8)) => { |v: Vec<char>| {
        let v: Vec<u32> = v.iter().map(|c| c.to_digit(16).unwrap()).collect();
        cp_from_u32((v[0] << 28) + (v[1] << 24) + (v[2] << 20) + (v[3] << 16) +
                    (v[4] << 12) + (v[5] << 8 ) + (v[6] << 4 ) + v[7])
      }}
    )
  )
);

named_args!(shortstring(quote: char) <StrSpan, PyStringContent>,
  fold_many0!(
    alt!(
      call!(escapedchar)
    | verify!(anychar, |c:char| c != quote) => { |c:char| Some(cp_from_char(c)) }
    ),
    PyStringContent::new(),
    |mut acc:PyStringContent, c:Option<PyStringCodePoint>| { match c { Some(c) => acc.push(c), None => () }; acc }
  )
);

named_args!(longstring(quote: char) <StrSpan, PyStringContent>,
  fold_many0!(
    alt!(
      call!(escapedchar)
    | verify!(tuple!(peek!(take!(3)), anychar), |(s,_):(StrSpan,_)| { s.fragment.0.chars().collect::<Vec<char>>() != vec![quote,quote,quote] }) => { |(_,c)| Some(cp_from_char(c)) }
    ),
    PyStringContent::new(),
    |mut acc:PyStringContent, c:Option<PyStringCodePoint>| { match c { Some(c) => acc.push(c), None => () }; acc }
  )
);

named_args!(shortrawstring(quote: char) <StrSpan, PyStringContent>,
  fold_many0!(
    alt!(
      tuple!(char!('\\'), anychar) => { |(c1,c2)| (cp_from_char(c1), Some(cp_from_char(c2))) }
    | verify!(none_of!("\\"), |c:char| c != quote) => { |c:char| (cp_from_char(c), None) }
    ),
    PyStringContent::new(),
    |mut acc:PyStringContent, (c1,c2):(PyStringCodePoint, Option<PyStringCodePoint>)| {
      acc.push(c1);
      match c2 { Some(c) => acc.push(c), None => () };
      acc
    }
  )
);

named_args!(longrawstring(quote: char) <StrSpan, PyStringContent>,
  fold_many0!(
    alt!(
      tuple!(char!('\\'), anychar) => { |(c1,c2)| (cp_from_char(c1), Some(cp_from_char(c2))) }
    | verify!(tuple!(peek!(take!(3)), none_of!("\\")), |(s,_):(StrSpan,_)| { s.fragment.0.chars().collect::<Vec<char>>() != vec![quote,quote,quote] }) => { |(_,c)| (cp_from_char(c), None) }
    ),
    PyStringContent::new(),
    |mut acc:PyStringContent, (c1,c2):(PyStringCodePoint, Option<PyStringCodePoint>)| {
      acc.push(c1);
      match c2 { Some(c) => acc.push(c), None => () };
      acc
    }
  )
);

named!(pub string<StrSpan, PyString>,
  do_parse!(
    prefix: alt!(tag!("fr")|tag!("Fr")|tag!("fR")|tag!("FR")|tag!("rf")|tag!("rF")|tag!("Rf")|tag!("RF")|tag!("r")|tag!("u")|tag!("R")|tag!("U")|tag!("f")|tag!("F")|tag!("")) >>
    is_raw: call!(|i, s:StrSpan| Ok((i, s.fragment.0.contains('r') || s.fragment.0.contains('R'))), prefix) >>
    content: switch!(call!(|i| Ok((i, is_raw))),
      false => alt!(
        delimited!(tag!("'''"), return_error!(call!(longstring, '\'')), tag!("'''"))
      | delimited!(tag!("\"\"\""), return_error!(call!(longstring, '"')), tag!("\"\"\""))
      | delimited!(char!('\''), return_error!(call!(shortstring, '\'')), char!('\''))
      | delimited!(char!('"'), return_error!(call!(shortstring, '"')), char!('"'))
      )
    | true => alt!(
        delimited!(tag!("'''"), return_error!(call!(longrawstring, '\'')), tag!("'''"))
      | delimited!(tag!("\"\"\""), return_error!(call!(longrawstring, '"')), tag!("\"\"\""))
      | delimited!(char!('\''), return_error!(call!(shortrawstring, '\'')), char!('\''))
      | delimited!(char!('"'), return_error!(call!(shortrawstring, '"')), char!('"'))
      )
    ) >> (PyString { prefix: prefix.to_string(), content: content })
  )
);
