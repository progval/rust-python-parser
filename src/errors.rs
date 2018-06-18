#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum PyParseError {
    UnexpectedIndent,
    ExpectedIndent,
}
impl From<PyParseError> for u32 {
    fn from(e: PyParseError) -> u32 {
        e as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nom;
    use nom::{Context, ErrorKind};
    use nom::types::CompleteStr;
    use nom_locate::LocatedSpan;

    use helpers::*;
    use statements::statement;


    #[test]
    fn if_no_condition() {
        assert_eq!(statement(make_strspan("if:\n foo"), 0), Err(
            nom::Err::Failure(
                Context::Code(
                    LocatedSpan { offset: 2, line: 1, fragment: CompleteStr(":\n foo") },
                    ErrorKind::Alt
                )
            )
        ));
    }
}
