use nom::anychar;

#[cfg(feature="wtf8")]
use wtf8;

use helpers::StrSpan;
use ast::*;

#[cfg(feature="wtf8")]
fn cp_from_char(c: char) -> wtf8::CodePoint {
    wtf8::CodePoint::from_char(c)
}
#[cfg(feature="wtf8")]
fn cp_from_u32(n: u32) -> Option<wtf8::CodePoint> {
    wtf8::CodePoint::from_u32(n)
}
#[cfg(not(feature="wtf8"))]
fn cp_from_char(c: char) -> char {
    c
}
#[cfg(not(feature="wtf8"))]
fn cp_from_u32(n: u32) -> Option<char> {
    ::std::char::from_u32(n)
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
    //| preceded!(char!('N'), delimited!(char!('{'), none_of!("}"), char!('}'))) => { |name|
    //    unicode_names::character(name)
    //  }
    | char!('N') => { |_| unimplemented!() }
    | preceded!(char!('u'), count!(one_of!("0123456789abcdefABCDEF"), 4)) => { |v: Vec<char>| {
        let it: Vec<u32> = v.iter().map(|c| c.to_digit(16).unwrap()).collect();
        if let [d1, d2, d3, d4] = &it[..] {
            cp_from_u32((d1 << 12) + (d2 << 8) + (d3 << 4) + d4)
        }
        else { unreachable!() }
      }}
    | preceded!(char!('U'), count!(one_of!("0123456789abcdefABCDEF"), 8)) => { |v: Vec<char>| {
        let it: Vec<u32> = v.iter().map(|c| c.to_digit(16).unwrap()).collect();
        if let [d1, d2, d3, d4, d5, d6, d7, d8] = &it[..] {
            cp_from_u32((d1 << 28) + (d2 << 24) + (d3 << 20) + (d4 << 16) +
                                  (d5 << 12) + (d6 << 8) + (d7 << 4) + d8)
        }
        else { unreachable!() }
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
        delimited!(tag!("'''"), call!(longstring, '\''), tag!("'''"))
      | delimited!(tag!("\"\"\""), call!(longstring, '"'), tag!("\"\"\""))
      | delimited!(char!('\''), call!(shortstring, '\''), char!('\''))
      | delimited!(char!('"'), call!(shortstring, '"'), char!('"'))
      )
    | true => alt!(
        delimited!(tag!("'''"), call!(longrawstring, '\''), tag!("'''"))
      | delimited!(tag!("\"\"\""), call!(longrawstring, '"'), tag!("\"\"\""))
      | delimited!(char!('\''), call!(shortrawstring, '\''), char!('\''))
      | delimited!(char!('"'), call!(shortrawstring, '"'), char!('"'))
      )
    ) >> (PyString { prefix: prefix.to_string(), content: content })
  )
);

