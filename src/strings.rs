use nom::anychar;

use helpers::StrSpan;
use ast::*;

named!(escapedchar<StrSpan, Option<char>>,
  preceded!(char!('\\'),
    alt!(
      char!('\n') => { |_| None }
    | char!('\\') => { |_| Some('\\') }
    | char!('\'') => { |_| Some('\'') }
    | char!('"') => { |_| Some('"') }
    | char!('b') => { |_| Some('\x07') } // BEL
    | char!('f') => { |_| Some('\x0c') } // FF
    | char!('n') => { |_| Some('\n') }
    | char!('r') => { |_| Some('\r') }
    | char!('t') => { |_| Some('\t') }
    | char!('v') => { |_| Some('\x0b') } // VT
    | tuple!(one_of!("01234567"), opt!(one_of!("01234567")), opt!(one_of!("01234567"))) => { |(c1, c2, c3): (char, Option<char>, Option<char>)|
        match (c1.to_digit(8), c2.and_then(|c| c.to_digit(8)), c3.and_then(|c| c.to_digit(8))) {
            (Some(d1), Some(d2), Some(d3)) => ::std::char::from_u32((d1 << 6) + (d2 << 3) + d3),
            (Some(d1), Some(d2), None    ) => ::std::char::from_u32((d1 << 3) + d2),
            (Some(d1), None,     None    ) => ::std::char::from_u32(d1),
            _ => unreachable!(),
        }
      }
    | preceded!(char!('x'), tuple!(one_of!("0123456789abcdefABCDEF"), one_of!("0123456789abcdefABCDEF"))) => { |(c1, c2): (char, char)|
        match (c1.to_digit(16), c2.to_digit(16)) {
            (Some(d1), Some(d2)) => ::std::char::from_u32((d1 << 4) + d2),
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
            ::std::char::from_u32((d1 << 12) + (d2 << 8) + (d3 << 4) + d4)
        }
        else { unreachable!() }
      }}
    | preceded!(char!('U'), count!(one_of!("0123456789abcdefABCDEF"), 8)) => { |v: Vec<char>| {
        let it: Vec<u32> = v.iter().map(|c| c.to_digit(16).unwrap()).collect();
        if let [d1, d2, d3, d4, d5, d6, d7, d8] = &it[..] {
            ::std::char::from_u32((d1 << 28) + (d2 << 24) + (d3 << 20) + (d4 << 16) +
                                  (d5 << 12) + (d6 << 8) + (d7 << 4) + d8)
        }
        else { unreachable!() }
      }}
    )
  )
);

named_args!(shortstring(quote: char) <StrSpan, String>,
  fold_many0!(
    alt!(
      call!(escapedchar)
    | verify!(none_of!("\\"), |c:char| c != quote) => { |c:char| Some(c) }
    ),
    String::new(),
    |mut acc:String, c:Option<char>| { match c { Some(c) => acc.push_str(&c.to_string()), None => () }; acc }
  )
);

named_args!(longstring(quote: char) <StrSpan, String>,
  fold_many0!(
    alt!(
      call!(escapedchar)
    | verify!(tuple!(peek!(take!(3)), none_of!("\\")), |(s,_):(StrSpan,_)| { s.fragment.0.chars().collect::<Vec<char>>() != vec![quote,quote,quote] }) => { |(_,c)| Some(c) }
    ),
    String::new(),
    |mut acc:String, c:Option<char>| { match c { Some(c) => acc.push_str(&c.to_string()), None => () }; acc }
  )
);

named_args!(shortrawstring(quote: char) <StrSpan, String>,
  fold_many0!(
    alt!(
      tuple!(char!('\\'), anychar) => { |(c1,c2)| (c1, Some(c2)) }
    | verify!(none_of!("\\"), |c:char| c != quote) => { |c:char| (c, None) }
    ),
    String::new(),
    |mut acc:String, (c1,c2):(char, Option<char>)| {
      acc.push(c1);
      match c2 { Some(c) => acc.push(c), None => () };
      acc
    }
  )
);

named_args!(longrawstring(quote: char) <StrSpan, String>,
  fold_many0!(
    alt!(
      tuple!(char!('\\'), anychar) => { |(c1,c2)| (c1, Some(c2)) }
    | verify!(tuple!(peek!(take!(3)), none_of!("\\")), |(s,_):(StrSpan,_)| { s.fragment.0.chars().collect::<Vec<char>>() != vec![quote,quote,quote] }) => { |(_,c)| (c, None) }
    ),
    String::new(),
    |mut acc:String, (c1,c2):(char, Option<char>)| {
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
    ) >> (PyString { prefix: prefix.to_string(), content: content.to_string() })
  )
);

