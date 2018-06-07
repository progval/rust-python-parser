use num_traits::Num;
use num_traits::Zero;

use helpers::StrSpan;
use ast::*;

// FIXME: Python does not allow two consecutive underscores, but I don't
// care enough to implement that check.
named!(integer<StrSpan, IntegerType>,
  alt!(
    many1!(one_of!("_0")) => { |_| IntegerType::zero() }
  | preceded!(not!(peek!(char!('0'))), many1!(one_of!("_0123456789"))) => { |s:Vec<char>|
      IntegerType::from_str_radix(&str::replace(&s.into_iter().collect::<String>(), "_", ""), 10).unwrap()
    }
  | preceded!(alt!(tag!("0b")|tag!("0B")), many1!(one_of!("_01"))) => { |s:Vec<char>|
      IntegerType::from_str_radix(&str::replace(&s.into_iter().collect::<String>(), "_", ""), 2).unwrap()
    }
  | preceded!(alt!(tag!("0o")|tag!("0O")), many1!(one_of!("_01234567"))) => { |s:Vec<char>|
      IntegerType::from_str_radix(&str::replace(&s.into_iter().collect::<String>(), "_", ""), 8).unwrap()
    }
  | preceded!(alt!(tag!("0x")|tag!("0X")), many1!(one_of!("_0123456789abcdefABCDEF"))) => { |s:Vec<char>|
      IntegerType::from_str_radix(&str::replace(&s.into_iter().collect::<String>(), "_", ""), 16).unwrap()
    }
  )
);

named!(j<StrSpan, bool>,
  map!(opt!(alt!(char!('j')|char!('J'))), |o| o.is_some())
);

named!(pub number<StrSpan, Expression>,
  alt!(
    tuple!(integer, j) => { |(i, imag)|
      if imag { Expression::ImaginaryInt(i) } else {Expression::Int(i) }
    }
  )
);
