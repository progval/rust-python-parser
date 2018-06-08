use std::str::FromStr;

#[cfg(feature="bigint")]
use num_traits::Num;

use helpers::StrSpan;
use ast::*;

named!(decimal_string<StrSpan, String>,
  map!(recognize!(tuple!(one_of!("0123456789"), many0!(one_of!("_0123456789")))), |s:StrSpan| str::replace(&s.fragment.0, "_", ""))
);

named!(decimal<StrSpan, IntegerType>,
  map!(decimal_string, |s:String|
    IntegerType::from_str_radix(&s, 10).unwrap()
  )
);

// FIXME: Python does not allow two consecutive underscores, but I don't
// care enough to implement that check.
named!(integer<StrSpan, IntegerType>,
  alt!(
    preceded!(not!(peek!(char!('0'))), decimal)
  | preceded!(alt!(tag!("0b")|tag!("0B")), recognize!(many1!(one_of!("_01")))) => { |s:StrSpan|
      IntegerType::from_str_radix(&str::replace(&s.fragment.0, "_", ""), 2).unwrap()
    }
  | preceded!(alt!(tag!("0o")|tag!("0O")), recognize!(many1!(one_of!("_01234567")))) => { |s:StrSpan|
      IntegerType::from_str_radix(&str::replace(&s.fragment.0, "_", ""), 8).unwrap()
    }
  | preceded!(alt!(tag!("0x")|tag!("0X")), recognize!(many1!(one_of!("_0123456789abcdefABCDEF")))) => { |s:StrSpan|
      IntegerType::from_str_radix(&str::replace(&s.fragment.0, "_", ""), 16).unwrap()
    }
  | tuple!(char!('0'), many0!(one_of!("_0"))) => { |_| 0u32.into() } // Either 0u64 or BigUint::zero()
  )
);

named!(float<StrSpan, f64>,
  alt!(
    // Case one: 42.
    map_res!(
      recognize!(tuple!(char!('.'),
        decimal_string,
        opt!(tuple!(one_of!("eE"), opt!(one_of!("+-")), decimal_string))
      )), |s:StrSpan| {
        f64::from_str(&str::replace(&s.fragment.0, "_", ""))
      }
    )
  | // Case two: 42e42 and 42.42e42
    map_res!(
      recognize!(tuple!(
        decimal_string,
        opt!(preceded!(char!('.'), decimal_string)),
        tuple!(one_of!("eE"), opt!(one_of!("+-")), decimal_string)
      )), |s:StrSpan| {
        f64::from_str(&str::replace(&s.fragment.0, "_", ""))
      }
    )
  | // Case three: 42. and 42.42
    map_res!(
      recognize!(tuple!(
        decimal_string,
        char!('.'),
        opt!(decimal_string)
      )), |s:StrSpan| {
        f64::from_str(&str::replace(&s.fragment.0, "_", ""))
      }
    )
  )
);

named!(pub number<StrSpan, Expression>,
  alt!(
    terminated!(decimal, one_of!("jJ")) =>  { |n| Expression::ImaginaryInt(n) }
  | tuple!(float, opt!(one_of!("jJ"))) => { |(n,j):(_,Option<_>)| if j.is_some() { Expression::ImaginaryFloat(n) } else { Expression::Float(n) } }
  | integer => { |n| Expression::Int(n) }
  )
);

#[cfg(test)]
mod tests {
    use super::*;
    use helpers::{make_strspan, assert_parse_eq};

    #[test]
    fn integer() {
        assert_parse_eq(number(make_strspan("0")), Ok((make_strspan(""),
            Expression::Int(0u32.into()))));
        assert_parse_eq(number(make_strspan("0000_000_0")), Ok((make_strspan(""),
            Expression::Int(0u32.into()))));
        assert_parse_eq(number(make_strspan("12345")), Ok((make_strspan(""),
            Expression::Int(12345u32.into()))));
        assert_parse_eq(number(make_strspan("0b101010")), Ok((make_strspan(""),
            Expression::Int(42u32.into()))));
        assert_parse_eq(number(make_strspan("0x2a")), Ok((make_strspan(""),
            Expression::Int(42u32.into()))));
        assert_parse_eq(number(make_strspan("0o52")), Ok((make_strspan(""),
            Expression::Int(42u32.into()))));
    }

    #[test]
    fn imag_integer() {
        assert_parse_eq(number(make_strspan("0j")), Ok((make_strspan(""),
            Expression::ImaginaryInt(0u32.into()))));
        assert_parse_eq(number(make_strspan("0000_000_0j")), Ok((make_strspan(""),
            Expression::ImaginaryInt(0u32.into()))));
        assert_parse_eq(number(make_strspan("12345j")), Ok((make_strspan(""),
            Expression::ImaginaryInt(12345u32.into()))));
    }

    #[test]
    fn float() {
        assert_parse_eq(number(make_strspan(".42")), Ok((make_strspan(""),
            Expression::Float(0.42))));
        assert_parse_eq(number(make_strspan("41.43")), Ok((make_strspan(""),
            Expression::Float(41.43))));
        assert_parse_eq(number(make_strspan("42.")), Ok((make_strspan(""),
            Expression::Float(42.))));

        assert_parse_eq(number(make_strspan(".42e10")), Ok((make_strspan(""),
            Expression::Float(0.42e10))));
        assert_parse_eq(number(make_strspan(".42e+10")), Ok((make_strspan(""),
            Expression::Float(0.42e10))));
        assert_parse_eq(number(make_strspan(".42e-10")), Ok((make_strspan(""),
            Expression::Float(0.42e-10))));

        assert_parse_eq(number(make_strspan("41.43e10")), Ok((make_strspan(""),
            Expression::Float(41.43e10))));
        assert_parse_eq(number(make_strspan("41.43e+10")), Ok((make_strspan(""),
            Expression::Float(41.43e10))));
        assert_parse_eq(number(make_strspan("41.43e-10")), Ok((make_strspan(""),
            Expression::Float(41.43e-10))));
    }

    #[test]
    fn imag_float() {
        assert_parse_eq(number(make_strspan(".42j")), Ok((make_strspan(""),
            Expression::ImaginaryFloat(0.42))));
        assert_parse_eq(number(make_strspan("41.43j")), Ok((make_strspan(""),
            Expression::ImaginaryFloat(41.43))));
        assert_parse_eq(number(make_strspan("42.j")), Ok((make_strspan(""),
            Expression::ImaginaryFloat(42.))));

        assert_parse_eq(number(make_strspan(".42e10j")), Ok((make_strspan(""),
            Expression::ImaginaryFloat(0.42e10))));
        assert_parse_eq(number(make_strspan(".42e+10j")), Ok((make_strspan(""),
            Expression::ImaginaryFloat(0.42e10))));
        assert_parse_eq(number(make_strspan(".42e-10j")), Ok((make_strspan(""),
            Expression::ImaginaryFloat(0.42e-10))));

        assert_parse_eq(number(make_strspan("41.43e10j")), Ok((make_strspan(""),
            Expression::ImaginaryFloat(41.43e10))));
        assert_parse_eq(number(make_strspan("41.43e+10j")), Ok((make_strspan(""),
            Expression::ImaginaryFloat(41.43e10))));
        assert_parse_eq(number(make_strspan("41.43e-10j")), Ok((make_strspan(""),
            Expression::ImaginaryFloat(41.43e-10))));
    }
}
