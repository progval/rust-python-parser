use std::cmp::min;

use nom::anychar;

use helpers::StrSpan;

named!(escapedchar<StrSpan, Option<u8>>,
  preceded!(char!('\\'),
    alt!(
      char!('\n') => { |_| None }
    | char!('\\') => { |_| Some(b'\\') }
    | char!('\'') => { |_| Some(b'\'') }
    | char!('"') => { |_| Some(b'"') }
    | char!('a') => { |_| Some(b'\x07') } // BEL
    | char!('b') => { |_| Some(b'\x08') } // BS
    | char!('f') => { |_| Some(b'\x0c') } // FF
    | char!('n') => { |_| Some(b'\n') }
    | char!('r') => { |_| Some(b'\r') }
    | char!('t') => { |_| Some(b'\t') }
    | char!('v') => { |_| Some(b'\x0b') } // VT
    | tuple!(one_of!("01234567"), opt!(one_of!("01234567")), opt!(one_of!("01234567"))) => { |(c1, c2, c3): (char, Option<char>, Option<char>)|
        match (c1.to_digit(8), c2.and_then(|c| c.to_digit(8)), c3.and_then(|c| c.to_digit(8))) {
            (Some(d1), Some(d2), Some(d3)) => Some(min((d1 << 6) + (d2 << 3) + d3, 255) as u8),
            (Some(d1), Some(d2), None    ) => Some(((d1 << 3) + d2) as u8),
            (Some(d1), None,     None    ) => Some(d1 as u8),
            _ => unreachable!(),
        }
      }
    | preceded!(char!('x'), tuple!(one_of!("0123456789abcdefABCDEF"), one_of!("0123456789abcdefABCDEF"))) => { |(c1, c2): (char, char)|
        match (c1.to_digit(16), c2.to_digit(16)) {
            (Some(d1), Some(d2)) => Some(((d1 << 4) + d2) as u8),
            _ => unreachable!(),
        }
      }
    )
  )
);

named_args!(shortbytes(quote: char) <StrSpan, Vec<u8>>,
  fold_many0!(
    alt!(
      call!(escapedchar)
    | verify!(anychar, |c:char| c != quote) => { |c:char| Some(c as u8) }
    ),
    Vec::new(),
    |mut acc:Vec<u8>, c:Option<u8>| { match c { Some(c) => acc.push(c), None => () }; acc }
  )
);

named_args!(longbytes(quote: char) <StrSpan, Vec<u8>>,
  fold_many0!(
    alt!(
      call!(escapedchar)
    | verify!(tuple!(peek!(take!(3)), anychar), |(s,_):(StrSpan,_)| { s.fragment.0.chars().collect::<Vec<char>>() != vec![quote,quote,quote] }) => { |(_,c)| Some(c as u8) }
    ),
    Vec::new(),
    |mut acc:Vec<u8>, c:Option<u8>| { match c { Some(c) => acc.push(c), None => () }; acc }
  )
);


named_args!(shortrawbytes(quote: char) <StrSpan, Vec<u8>>,
  fold_many0!(
    alt!(
      tuple!(char!('\\'), anychar) => { |(c1,c2)| (c1 as u8, Some(c2 as u8)) }
    | verify!(anychar, |c:char| c != quote) => { |c:char| (c as u8, None) }
    ),
    Vec::new(),
    |mut acc:Vec<u8>, (c1,c2):(u8, Option<u8>)| {
      acc.push(c1);
      match c2 { Some(c) => acc.push(c), None => () };
      acc
    }
  )
);

named_args!(longrawbytes(quote: char) <StrSpan, Vec<u8>>,
  fold_many0!(
    alt!(
      tuple!(char!('\\'), anychar) => { |(c1,c2)| (c1 as u8, Some(c2 as u8)) }
    | verify!(tuple!(peek!(take!(3)), none_of!("\\")), |(s,_):(StrSpan,_)| { s.fragment.0.chars().collect::<Vec<char>>() != vec![quote,quote,quote] }) => { |(_,c)| (c as u8, None) }
    ),
    Vec::new(),
    |mut acc:Vec<u8>, (c1,c2):(u8, Option<u8>)| {
      acc.push(c1);
      match c2 { Some(c) => acc.push(c), None => () };
      acc
    }
  )
);


named!(pub bytes<StrSpan, Vec<u8>>,
  do_parse!(
    prefix: alt!(tag!("br")|tag!("Br")|tag!("bR")|tag!("BR")|tag!("rb")|tag!("rB")|tag!("Rb")|tag!("RB")|tag!("b")|tag!("B")|tag!("")) >>
    is_raw: call!(|i, s:StrSpan| Ok((i, s.fragment.0.contains('r') || s.fragment.0.contains('R'))), prefix) >>
    content: switch!(call!(|i| Ok((i, is_raw))),
      false => alt!(
        delimited!(tag!("'''"), call!(longbytes, '\''), tag!("'''"))
      | delimited!(tag!("\"\"\""), call!(longbytes, '"'), tag!("\"\"\""))
      | delimited!(char!('\''), call!(shortbytes, '\''), char!('\''))
      | delimited!(char!('"'), call!(shortbytes, '"'), char!('"'))
      )
    | true => alt!(
        delimited!(tag!("'''"), call!(longrawbytes, '\''), tag!("'''"))
      | delimited!(tag!("\"\"\""), call!(longrawbytes, '"'), tag!("\"\"\""))
      | delimited!(char!('\''), call!(shortrawbytes, '\''), char!('\''))
      | delimited!(char!('"'), call!(shortrawbytes, '"'), char!('"'))
      )
    ) >> (content)
  )
);
