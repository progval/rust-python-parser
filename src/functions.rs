use std::marker::PhantomData;

use nom::IResult;

use statements::{ImportParser, block};
use expressions::ExpressionParser;
use helpers::*;
use ast::*;

/*********************************************************************
 * Decorators
 *********************************************************************/

// decorator: '@' dotted_name [ '(' [arglist] ')' ] NEWLINE
named_args!(decorator(indent: usize) <StrSpan, Decorator>,
  do_parse!(
    count!(char!(' '), indent) >>
    char!('@') >>
    name: ws2!(call!(ImportParser::<NewlinesAreNotSpaces>::dotted_name)) >>
    args: opt!(ws2!(delimited!(char!('('), ws4!(call!(ExpressionParser::<NewlinesAreSpaces>::arglist)), char!(')')))) >>
    newline >> (
      Decorator { name, args }
    )
  )
);

// decorators: decorator+
named_args!(decorators(indent: usize) <StrSpan, Vec<Decorator>>,
  many0!(call!(decorator, indent))
);

// decorated: decorators (classdef | funcdef | async_funcdef)
named_args!(pub decorated(indent: usize) <StrSpan, CompoundStatement>,
  do_parse!(
    decorators: call!(decorators, indent) >>
    s: switch!(peek!(ws2!(first_word)),
        "def" => call!(funcdef, indent, decorators.clone()) // FIXME: do not clone
      | "async" => call!(funcdef, indent, decorators.clone()) // FIXME: do not clone
      | "class" => call!(classdef, indent, decorators)
    ) >> (s)
  )
);

/*********************************************************************
 * Function definition
 *********************************************************************/

// async_funcdef: ASYNC funcdef
// funcdef: 'def' NAME parameters ['->' test] ':' suite
named_args!(funcdef(indent: usize, decorators: Vec<Decorator>) <StrSpan, CompoundStatement>,
  do_parse!(
    count!(char!(' '), indent) >>
    async: opt!(tuple!(tag!("async"), space_sep2)) >>
    tag!("def") >>
    space_sep2 >>
    name: name >>
    parameters: ws2!(parameters) >>
    return_type: opt!(ws2!(preceded!(tag!("->"), call!(ExpressionParser::<NewlinesAreNotSpaces>::test)))) >>
    ws2!(char!(':')) >>
    code: call!(block, indent) >> (
      CompoundStatement::Funcdef(Funcdef {
          async: async.is_some(), decorators, name, parameters, return_type: return_type.map(|t| *t), code
      })
    )
  )
);

// classdef: 'class' NAME ['(' [arglist] ')'] ':' suite
named_args!(classdef(indent: usize, decorators: Vec<Decorator>) <StrSpan, CompoundStatement>,
  do_parse!(
    count!(char!(' '), indent) >>
    tag!("class") >>
    space_sep2 >>
    name: name >>
    spaces >>
    arguments: opt!(ws2!(delimited!(char!('('), ws4!(call!(ExpressionParser::<NewlinesAreSpaces>::arglist)), char!(')')))) >>
    ws2!(char!(':')) >> 
    code: call!(block, indent) >> (
      CompoundStatement::Classdef(Classdef {
          decorators, name, arguments: arguments.unwrap_or_default(), code
      })
    )
  )
);

/*********************************************************************
 * Function parameters
 *********************************************************************/

trait IsItTyped {
    type Return: Clone; // FIXME: do not require Clone
    type List;

    fn fpdef<'a>(input: StrSpan<'a>) -> IResult<StrSpan<'a>, Self::Return, u32>;

    fn fpdef_with_default<'a>(i: StrSpan<'a>) -> IResult<StrSpan<'a>, (Self::Return, Option<Box<Expression>>), u32> {
        ws4!(i, tuple!(
            Self::fpdef,
            opt!(
                preceded!(
                    ws4!(char!('=')),
                    call!(ExpressionParser::<NewlinesAreSpaces>::test)
                )
            )
        ))
    }

    fn make_list(positional_args: Vec<(Self::Return, Option<Box<Expression>>)>, star_args: Option<Option<Self::Return>>, keyword_args: Vec<(Self::Return, Option<Box<Expression>>)>, star_kwargs: Option<Self::Return>) -> Self::List;
}

// For typed parameter lists
struct Untyped;
impl IsItTyped for Typed {
    type Return = (Name, Option<Box<Expression>>);
    type List = TypedArgsList;

    named!(fpdef<StrSpan, Self::Return>,
      ws4!(tuple!(name,
        opt!(ws4!(preceded!(char!(':'), call!(ExpressionParser::<NewlinesAreSpaces>::test))))
      ))
    );

    fn make_list(positional_args: Vec<(Self::Return, Option<Box<Expression>>)>, star_args: Option<Option<Self::Return>>, keyword_args: Vec<(Self::Return, Option<Box<Expression>>)>, star_kwargs: Option<Self::Return>) -> Self::List {
        let deref_option = |o: Option<Box<_>>| o.map(|v| *v);
        TypedArgsList {
            positional_args: positional_args.into_iter().map(|((name, typed), value)|
                (name, deref_option(typed), deref_option(value))
            ).collect(),
            star_args: match star_args {
                Some(Some((name, typed))) => StarParams::Named((name, deref_option(typed))),
                Some(None) => StarParams::Anonymous,
                None => StarParams::No,
            },
            keyword_args: keyword_args.into_iter().map(|((name, typed), value)|
                (name, deref_option(typed), deref_option(value))
            ).collect(),
            star_kwargs: star_kwargs.map(|(name, typed)| (name, deref_option(typed)))
        }
    }
}

// For untyped parameter lists
struct Typed;
impl IsItTyped for Untyped {
    type Return = Name;
    type List = UntypedArgsList;

    named!(fpdef<StrSpan, Self::Return>,
      tuple!(name)
    );

    fn make_list(positional_args: Vec<(Self::Return, Option<Box<Expression>>)>, star_args: Option<Option<Self::Return>>, keyword_args: Vec<(Self::Return, Option<Box<Expression>>)>, star_kwargs: Option<Self::Return>) -> Self::List {
        let deref_option = |o: Option<Box<_>>| o.map(|v| *v);
        UntypedArgsList {
            positional_args: positional_args.into_iter().map(|(name, value)|
                (name, deref_option(value))
            ).collect(),
            star_args: match star_args {
                Some(Some(name)) => StarParams::Named(name),
                Some(None) => StarParams::Anonymous,
                None => StarParams::No,
            },
            keyword_args: keyword_args.into_iter().map(|(name, value)|
                (name, deref_option(value))
            ).collect(),
            star_kwargs
        }
    }
}

// parameters: '(' [typedargslist] ')'
named!(parameters<StrSpan, TypedArgsList>,
  map!(delimited!(char!('('), opt!(ws4!(typedargslist)), char!(')')), |o| o.unwrap_or_default())
);

// typedargslist: (tfpdef ['=' test] (',' tfpdef ['=' test])* [',' [
//         '*' [tfpdef] (',' tfpdef ['=' test])* [',' ['**' tfpdef [',']]]
//       | '**' tfpdef [',']]]
//   | '*' [tfpdef] (',' tfpdef ['=' test])* [',' ['**' tfpdef [',']]]
//   | '**' tfpdef [','])
//
// tfpdef: NAME [':' test]
//
// varargslist: (vfpdef ['=' test] (',' vfpdef ['=' test])* [',' [
//         '*' [vfpdef] (',' vfpdef ['=' test])* [',' ['**' vfpdef [',']]]
//       | '**' vfpdef [',']]]
//   | '*' [vfpdef] (',' vfpdef ['=' test])* [',' ['**' vfpdef [',']]]
//   | '**' vfpdef [',']
// )
//
// vfpdef: NAME

struct ParamlistParser<IIT: IsItTyped> {
    phantom: PhantomData<IIT>
}
impl<IIT: IsItTyped> ParamlistParser<IIT> {
    named!(parse<StrSpan, IIT::List>, ws4!(
      alt!(
      /***************************
       * Case 1: only **kwargs
       ***************************/
        do_parse!( // Parse this part: '**' tfpdef [',']
          tag!("**") >>
          star_kwargs: call!(IIT::fpdef) >> (
            IIT::make_list(Vec::new(), None, Vec::new(), Some(star_kwargs))
          )
        )

      /***************************
       * Case 2: Starts with *args
       ***************************/
      | do_parse!( // Parse this part: '*' [tfpdef] (',' tfpdef ['=' test])* [',' ['**' tfpdef [',']]]
          tag!("*") >>
          star_args: opt!(call!(IIT::fpdef)) >>
          keyword_args: many0!(preceded!(char!(','), call!(IIT::fpdef_with_default))) >>
          star_kwargs: opt!(ws4!(preceded!(char!(','), opt!(ws4!(preceded!(tag!("**"), call!(IIT::fpdef))))))) >>
          opt!(ws4!(char!(','))) >> (
            IIT::make_list(Vec::new(), Some(star_args), keyword_args, star_kwargs.unwrap_or(None))
          )
        )

      /***************************
       * Case 3: Starts with a positional argument
       ***************************/
      | do_parse!(

          /************
           * Parse positional arguments:
           * tfpdef ['=' test] (',' tfpdef ['=' test])*
           */
          positional_args: separated_nonempty_list!(ws4!(char!(',')), call!(IIT::fpdef_with_default)) >>
          r: opt!(ws4!(preceded!(char!(','), opt!(ws4!(

            alt!(
              /************
               * Case 3a: positional arguments are immediately followed by **kwargs
               * Parse this: '**' tfpdef [',']
               */
              preceded!(tag!("**"), call!(IIT::fpdef)) => {|kwargs|
                IIT::make_list(positional_args.clone(), None, Vec::new(), Some(kwargs)) // FIXME: do not clone
              }

              /************
               * Case 3b: positional arguments are followed by * or *args
               * Parse this: '*' [tfpdef] (',' tfpdef ['=' test])* [',' ['**' tfpdef [',']]]
               */
            | do_parse!(
                char!('*') >>
                star_args: opt!(call!(IIT::fpdef)) >>
                keyword_args: opt!(ws4!(preceded!(char!(','), separated_nonempty_list!(ws4!(char!(',')), call!(IIT::fpdef_with_default))))) >>
                star_kwargs: opt!(ws4!(preceded!(char!(','), opt!(preceded!(tag!("**"), call!(IIT::fpdef)))))) >> ( // FIXME: ws! is needed here because it does not traverse opt!
                  IIT::make_list(positional_args.clone(), Some(star_args), keyword_args.unwrap_or(Vec::new()), star_kwargs.unwrap_or(None)) // FIXME: do not clone
                )
              )

            )
          ))))) >> (
            /************
             * Case 3c: positional arguments are not followed by anything
             */
            match r {
                Some(Some(r)) => r,
                Some(None) |
                None => IIT::make_list(positional_args, None, Vec::new(), None),
            }
          )
        )
      )
    ));
}

pub(crate) fn typedargslist(i: StrSpan) -> IResult<StrSpan, TypedArgsList, u32> {
    ParamlistParser::<Typed>::parse(i)
}

pub(crate) fn varargslist(i: StrSpan) -> IResult<StrSpan, UntypedArgsList, u32> {
    ParamlistParser::<Untyped>::parse(i)
}

#[cfg(test)]
mod tests {
    use super::*;
    use helpers::{make_strspan, assert_parse_eq};

    #[test]
    fn test_decorator() {
        assert_parse_eq(decorator(make_strspan("@foo\n"), 0), Ok((make_strspan(""),
            Decorator {
                name: vec!["foo".to_string()],
                args: None,
            }
        )));
        assert_parse_eq(decorator(make_strspan("@foo.bar\n"), 0), Ok((make_strspan(""),
            Decorator {
                name: vec!["foo".to_string(), "bar".to_string()],
                args: None,
            }
        )));

        assert_parse_eq(decorator(make_strspan("@foo(baz)\n"), 0), Ok((make_strspan(""),
            Decorator {
                name: vec!["foo".to_string()],
                args: Some(
                    vec![Argument::Positional(Expression::Name("baz".to_string()))],
                )
            }
        )));
        assert_parse_eq(decorator(make_strspan("@foo.bar(baz)\n"), 0), Ok((make_strspan(""),
            Decorator {
                name: vec!["foo".to_string(), "bar".to_string()],
                args: Some(
                    vec![Argument::Positional(Expression::Name("baz".to_string()))],
                )
            }
        )));
        assert_parse_eq(decorator(make_strspan("  @foo.bar(baz)\n"), 2), Ok((make_strspan(""),
            Decorator {
                name: vec!["foo".to_string(), "bar".to_string()],
                args: Some(
                    vec![Argument::Positional(Expression::Name("baz".to_string()))],
                )
            }
        )));
    }

    #[test]
    fn test_funcdef() {
        assert_parse_eq(decorated(make_strspan("def foo():\n bar"), 0), Ok((make_strspan(""),
            CompoundStatement::Funcdef(Funcdef {
                async: false,
                decorators: vec![],
                name: "foo".to_string(),
                parameters: TypedArgsList::default(),
                return_type: None,
                code: vec![Statement::Assignment(vec![Expression::Name("bar".to_string())], vec![])],
            })
        )));

        assert_parse_eq(decorated(make_strspan(" def foo():\n  bar"), 1), Ok((make_strspan(""),
            CompoundStatement::Funcdef(Funcdef {
                async: false,
                decorators: vec![],
                name: "foo".to_string(),
                parameters: TypedArgsList::default(),
                return_type: None,
                code: vec![Statement::Assignment(vec![Expression::Name("bar".to_string())], vec![])],
            })
        )));

        assert!(decorated(make_strspan(" def foo():\n bar"), 1).is_err());
    }

    #[test]
    fn test_decorated_func() {
        assert_parse_eq(decorated(make_strspan(" @foo\n def foo():\n  bar"), 1), Ok((make_strspan(""),
            CompoundStatement::Funcdef(Funcdef {
                async: false,
                decorators: vec![
                    Decorator {
                        name: vec!["foo".to_string()],
                        args: None
                    },
                ],
                name: "foo".to_string(),
                parameters: TypedArgsList::default(),
                return_type: None,
                code: vec![Statement::Assignment(vec![Expression::Name("bar".to_string())], vec![])],
            })
        )));
    }

    #[test]
    fn test_positional() {
        assert_parse_eq(ParamlistParser::<Typed>::parse(make_strspan("foo")), Ok((make_strspan(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None, None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_parse_eq(ParamlistParser::<Untyped>::parse(make_strspan("foo")), Ok((make_strspan(""),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_parse_eq(ParamlistParser::<Typed>::parse(make_strspan("foo=bar")), Ok((make_strspan(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None, Some(Expression::Name("bar".to_string()))),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_parse_eq(ParamlistParser::<Untyped>::parse(make_strspan("foo=bar")), Ok((make_strspan(""),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), Some(Expression::Name("bar".to_string()))),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_parse_eq(ParamlistParser::<Typed>::parse(make_strspan("foo:bar")), Ok((make_strspan(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), Some(Expression::Name("bar".to_string())), None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_parse_eq(ParamlistParser::<Untyped>::parse(make_strspan("foo:bar")), Ok((make_strspan(":bar"),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_parse_eq(ParamlistParser::<Typed>::parse(make_strspan("foo:bar=baz")), Ok((make_strspan(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), Some(Expression::Name("bar".to_string())), Some(Expression::Name("baz".to_string()))),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_parse_eq(ParamlistParser::<Untyped>::parse(make_strspan("foo:bar=baz")), Ok((make_strspan(":bar=baz"),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_parse_eq(ParamlistParser::<Typed>::parse(make_strspan("foo, bar")), Ok((make_strspan(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None, None),
                    ("bar".to_string(), None, None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_parse_eq(ParamlistParser::<Untyped>::parse(make_strspan("foo, bar")), Ok((make_strspan(""),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None),
                    ("bar".to_string(), None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));
    }

    #[test]
    fn test_star_args() {
        assert_parse_eq(ParamlistParser::<Typed>::parse(make_strspan("foo, *, bar")), Ok((make_strspan(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None, None),
                ],
                star_args: StarParams::Anonymous,
                keyword_args: vec![
                    ("bar".to_string(), None, None),
                ],
                star_kwargs: None,
            }
        )));

        assert_parse_eq(ParamlistParser::<Untyped>::parse(make_strspan("foo, *, bar")), Ok((make_strspan(""),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None),
                ],
                star_args: StarParams::Anonymous,
                keyword_args: vec![
                    ("bar".to_string(), None),
                ],
                star_kwargs: None,
            }
        )));

        assert_parse_eq(ParamlistParser::<Typed>::parse(make_strspan("foo, *, bar=baz")), Ok((make_strspan(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None, None),
                ],
                star_args: StarParams::Anonymous,
                keyword_args: vec![
                    ("bar".to_string(), None, Some(Expression::Name("baz".to_string()))),
                ],
                star_kwargs: None,
            }
        )));

        assert_parse_eq(ParamlistParser::<Untyped>::parse(make_strspan("foo, *, bar=baz")), Ok((make_strspan(""),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None),
                ],
                star_args: StarParams::Anonymous,
                keyword_args: vec![
                    ("bar".to_string(), Some(Expression::Name("baz".to_string()))),
                ],
                star_kwargs: None,
            }
        )));
    }

    #[test]
    fn test_star_kwargs() {
        assert_parse_eq(ParamlistParser::<Typed>::parse(make_strspan("foo, **kwargs")), Ok((make_strspan(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None, None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![
                ],
                star_kwargs: Some(("kwargs".to_string(), None)),
            }
        )));

        assert_parse_eq(ParamlistParser::<Untyped>::parse(make_strspan("foo, **kwargs")), Ok((make_strspan(""),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![
                ],
                star_kwargs: Some("kwargs".to_string()),
            }
        )));

        assert_parse_eq(ParamlistParser::<Typed>::parse(make_strspan("foo, *args, **kwargs")), Ok((make_strspan(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None, None),
                ],
                star_args: StarParams::Named(("args".to_string(), None)),
                keyword_args: vec![
                ],
                star_kwargs: Some(("kwargs".to_string(), None)),
            }
        )));

        assert_parse_eq(ParamlistParser::<Untyped>::parse(make_strspan("foo, *args, **kwargs")), Ok((make_strspan(""),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None),
                ],
                star_args: StarParams::Named("args".to_string()),
                keyword_args: vec![
                ],
                star_kwargs: Some("kwargs".to_string()),
            }
        )));

        assert_parse_eq(ParamlistParser::<Typed>::parse(make_strspan("foo, *, bar, **kwargs")), Ok((make_strspan(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None, None),
                ],
                star_args: StarParams::Anonymous,
                keyword_args: vec![
                    ("bar".to_string(), None, None),
                ],
                star_kwargs: Some(("kwargs".to_string(), None)),
            }
        )));

        assert_parse_eq(ParamlistParser::<Untyped>::parse(make_strspan("foo, *, bar, **kwargs")), Ok((make_strspan(""),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None),
                ],
                star_args: StarParams::Anonymous,
                keyword_args: vec![
                    ("bar".to_string(), None),
                ],
                star_kwargs: Some("kwargs".to_string()),
            }
        )));
    }

    #[test]
    fn test_starargs_first() {
        assert_parse_eq(ParamlistParser::<Untyped>::parse(make_strspan("*foo, bar, **kwargs")), Ok((make_strspan(""),
            UntypedArgsList {
                positional_args: vec![
                ],
                star_args: StarParams::Named("foo".to_string()),
                keyword_args: vec![
                    ("bar".to_string(), None),
                ],
                star_kwargs: Some("kwargs".to_string()),
            }
        )));

        assert_parse_eq(ParamlistParser::<Untyped>::parse(make_strspan("*foo, **kwargs")), Ok((make_strspan(""),
            UntypedArgsList {
                positional_args: vec![
                ],
                star_args: StarParams::Named("foo".to_string()),
                keyword_args: vec![
                ],
                star_kwargs: Some("kwargs".to_string()),
            }
        )));
    }
}
