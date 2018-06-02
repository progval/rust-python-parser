use std::marker::PhantomData;

use nom::types::CompleteStr;
use nom::IResult;

use statements::{ImportParser, block};
use statements::{CompoundStatement, Funcdef, Classdef};
use expressions::{Expression, ExpressionParser, Arglist};
use helpers::{name, Name, newline, space_sep2};
use helpers::{NewlinesAreSpaces, NewlinesAreNotSpaces};

/*********************************************************************
 * Decorators
 *********************************************************************/

#[derive(Clone, Debug, PartialEq)]
pub struct Decorator {
    name: Vec<Name>,
    args: Option<Arglist>,
}

// decorator: '@' dotted_name [ '(' [arglist] ')' ] NEWLINE
named_args!(decorator(indent: usize) <CompleteStr, Decorator>,
  preceded!(count!(char!(' '), indent),
    ws2!(do_parse!(
      char!('@') >>
      name: call!(ImportParser::<NewlinesAreNotSpaces>::dotted_name) >>
      args: opt!(ws2!(delimited!(char!('('), ws!(call!(ExpressionParser::<NewlinesAreSpaces>::arglist)), char!(')')))) >>
      newline >> (
        Decorator { name, args }
      )
    ))
  )
);

// decorators: decorator+
named_args!(decorators(indent: usize) <CompleteStr, Vec<Decorator>>,
  many0!(call!(decorator, indent))
);

// decorated: decorators (classdef | funcdef | async_funcdef)
named_args!(pub decorated(indent: usize) <CompleteStr, CompoundStatement>,
  do_parse!(
    decorators: call!(decorators, indent) >>
    s: alt!(
        call!(funcdef, indent, decorators.clone()) // FIXME: do not clone
      | call!(classdef, indent, decorators)
    ) >> (s)
  )
);

/*********************************************************************
 * Function definition
 *********************************************************************/

// async_funcdef: ASYNC funcdef
// funcdef: 'def' NAME parameters ['->' test] ':' suite
named_args!(funcdef(indent: usize, decorators: Vec<Decorator>) <CompleteStr, CompoundStatement>,
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
named_args!(classdef(indent: usize, decorators: Vec<Decorator>) <CompleteStr, CompoundStatement>,
  do_parse!(
    count!(char!(' '), indent) >>
    tag!("class") >>
    space_sep2 >>
    name: name >>
    parameters: ws2!(delimited!(char!('('), ws!(call!(ExpressionParser::<NewlinesAreSpaces>::arglist)), char!(')'))) >>
    ws2!(char!(':')) >> 
    code: call!(block, indent) >> (
      CompoundStatement::Classdef(Classdef {
          decorators, name, parameters, code
      })
    )
  )
);

/*********************************************************************
 * Function parameters
 *********************************************************************/

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StarParams<T> {
    /// No single star
    No,
    /// `*` alone, with no name
    Anonymous,
    /// *args` or `*args:type`
    Named(T),
}

impl<T> Default for StarParams<T> {
    fn default() -> StarParams<T> {
        StarParams::No
    }
}

#[derive(Clone, Debug, PartialEq, Default,)]
pub struct TypedArgsList {
    positional_args: Vec<(Name, Option<Expression>, Option<Expression>)>,
    star_args: StarParams<(Name, Option<Expression>)>,
    keyword_args: Vec<(Name, Option<Expression>, Option<Expression>)>,
    star_kwargs: Option<(Name, Option<Expression>)>,
}

#[derive(Clone, Debug, PartialEq, Default)]
pub struct UntypedArgsList {
    positional_args: Vec<(Name, Option<Expression>)>,
    star_args: StarParams<Name>,
    keyword_args: Vec<(Name, Option<Expression>)>,
    star_kwargs: Option<Name>,
}

trait IsItTyped {
    type Return: Clone; // FIXME: do not require Clone
    type List;

    fn fpdef<'a>(input: CompleteStr<'a>) -> IResult<CompleteStr<'a>, Self::Return, u32>;

    fn fpdef_with_default<'a>(i: CompleteStr<'a>) -> IResult<CompleteStr<'a>, (Self::Return, Option<Box<Expression>>), u32> {
        ws!(i, tuple!(
            Self::fpdef,
            opt!(
                preceded!(
                    char!('='),
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

    named!(fpdef<CompleteStr, Self::Return>,
      ws!(tuple!(name,
        opt!(preceded!(char!(':'), call!(ExpressionParser::<NewlinesAreSpaces>::test)))
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

    named!(fpdef<CompleteStr, Self::Return>,
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
named!(parameters<CompleteStr, TypedArgsList>,
  map!(delimited!(char!('('), opt!(ws!(typedargslist)), char!(')')), |o| o.unwrap_or_default())
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
    named!(parse<CompleteStr, IIT::List>, ws!(
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
          keyword_args: separated_list!(char!(','), call!(IIT::fpdef_with_default)) >>
          star_kwargs: opt!(preceded!(char!(','), opt!(preceded!(tag!("**"), call!(IIT::fpdef))))) >> (
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
          positional_args: separated_nonempty_list!(char!(','), call!(IIT::fpdef_with_default)) >>
          r: opt!(ws!(preceded!(char!(','), opt!( // FIXME: ws! is needed here because it does not traverse opt!

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
                keyword_args: opt!(preceded!(char!(','), separated_nonempty_list!(char!(','), call!(IIT::fpdef_with_default)))) >>
                star_kwargs: opt!(ws!(preceded!(char!(','), opt!(preceded!(tag!("**"), call!(IIT::fpdef)))))) >> ( // FIXME: ws! is needed here because it does not traverse opt!
                  IIT::make_list(positional_args.clone(), Some(star_args), keyword_args.unwrap_or(Vec::new()), star_kwargs.unwrap_or(None)) // FIXME: do not clone
                )
              )

            )
          )))) >> (
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

pub(crate) fn typedargslist(i: CompleteStr) -> IResult<CompleteStr, TypedArgsList, u32> {
    ParamlistParser::<Typed>::parse(i)
}

pub(crate) fn varargslist(i: CompleteStr) -> IResult<CompleteStr, UntypedArgsList, u32> {
    ParamlistParser::<Untyped>::parse(i)
}

#[cfg(test)]
mod tests {
    use super::*;
    use nom::types::CompleteStr as CS;
    use expressions::{Argument, Atom};
    use statements::Statement;

    #[test]
    fn test_decorator() {
        assert_eq!(decorator(CS("@foo\n"), 0), Ok((CS(""),
            Decorator {
                name: vec!["foo".to_string()],
                args: None,
            }
        )));
        assert_eq!(decorator(CS("@foo.bar\n"), 0), Ok((CS(""),
            Decorator {
                name: vec!["foo".to_string(), "bar".to_string()],
                args: None,
            }
        )));

        assert_eq!(decorator(CS("@foo(baz)\n"), 0), Ok((CS(""),
            Decorator {
                name: vec!["foo".to_string()],
                args: Some(Arglist {
                    positional_args: vec![Argument::Normal(Expression::Atom(Atom::Name("baz".to_string())))],
                    keyword_args: Vec::new(),
                })
            }
        )));
        assert_eq!(decorator(CS("@foo.bar(baz)\n"), 0), Ok((CS(""),
            Decorator {
                name: vec!["foo".to_string(), "bar".to_string()],
                args: Some(Arglist {
                    positional_args: vec![Argument::Normal(Expression::Atom(Atom::Name("baz".to_string())))],
                    keyword_args: Vec::new(),
                })
            }
        )));
    }

    #[test]
    fn test_funcdef() {
        assert_eq!(decorated(CS("def foo():\n bar"), 0), Ok((CS(""),
            CompoundStatement::Funcdef(Funcdef {
                async: false,
                decorators: vec![],
                name: "foo".to_string(),
                parameters: TypedArgsList::default(),
                return_type: None,
                code: vec![Statement::Expressions(vec![Expression::Atom(Atom::Name("bar".to_string()))])],
            })
        )));

        assert_eq!(decorated(CS(" def foo():\n  bar"), 1), Ok((CS(""),
            CompoundStatement::Funcdef(Funcdef {
                async: false,
                decorators: vec![],
                name: "foo".to_string(),
                parameters: TypedArgsList::default(),
                return_type: None,
                code: vec![Statement::Expressions(vec![Expression::Atom(Atom::Name("bar".to_string()))])],
            })
        )));

        assert!(decorated(CS(" def foo():\n bar"), 1).is_err());
    }

    #[test]
    fn test_positional() {
        assert_eq!(ParamlistParser::<Typed>::parse(CS("foo")), Ok((CS(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None, None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_eq!(ParamlistParser::<Untyped>::parse(CS("foo")), Ok((CS(""),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_eq!(ParamlistParser::<Typed>::parse(CS("foo=bar")), Ok((CS(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None, Some(Expression::Atom(Atom::Name("bar".to_string())))),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_eq!(ParamlistParser::<Untyped>::parse(CS("foo=bar")), Ok((CS(""),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), Some(Expression::Atom(Atom::Name("bar".to_string())))),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_eq!(ParamlistParser::<Typed>::parse(CS("foo:bar")), Ok((CS(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), Some(Expression::Atom(Atom::Name("bar".to_string()))), None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_eq!(ParamlistParser::<Untyped>::parse(CS("foo:bar")), Ok((CS(":bar"),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_eq!(ParamlistParser::<Typed>::parse(CS("foo:bar=baz")), Ok((CS(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), Some(Expression::Atom(Atom::Name("bar".to_string()))), Some(Expression::Atom(Atom::Name("baz".to_string())))),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_eq!(ParamlistParser::<Untyped>::parse(CS("foo:bar=baz")), Ok((CS(":bar=baz"),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None),
                ],
                star_args: StarParams::No,
                keyword_args: vec![],
                star_kwargs: None,
            }
        )));

        assert_eq!(ParamlistParser::<Typed>::parse(CS("foo, bar")), Ok((CS(""),
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

        assert_eq!(ParamlistParser::<Untyped>::parse(CS("foo, bar")), Ok((CS(""),
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
        assert_eq!(ParamlistParser::<Typed>::parse(CS("foo, *, bar")), Ok((CS(""),
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

        assert_eq!(ParamlistParser::<Untyped>::parse(CS("foo, *, bar")), Ok((CS(""),
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

        assert_eq!(ParamlistParser::<Typed>::parse(CS("foo, *, bar=baz")), Ok((CS(""),
            TypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None, None),
                ],
                star_args: StarParams::Anonymous,
                keyword_args: vec![
                    ("bar".to_string(), None, Some(Expression::Atom(Atom::Name("baz".to_string())))),
                ],
                star_kwargs: None,
            }
        )));

        assert_eq!(ParamlistParser::<Untyped>::parse(CS("foo, *, bar=baz")), Ok((CS(""),
            UntypedArgsList {
                positional_args: vec![
                    ("foo".to_string(), None),
                ],
                star_args: StarParams::Anonymous,
                keyword_args: vec![
                    ("bar".to_string(), Some(Expression::Atom(Atom::Name("baz".to_string())))),
                ],
                star_kwargs: None,
            }
        )));
    }

    #[test]
    fn test_star_kwargs() {
        assert_eq!(ParamlistParser::<Typed>::parse(CS("foo, **kwargs")), Ok((CS(""),
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

        assert_eq!(ParamlistParser::<Untyped>::parse(CS("foo, **kwargs")), Ok((CS(""),
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

        assert_eq!(ParamlistParser::<Typed>::parse(CS("foo, *args, **kwargs")), Ok((CS(""),
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

        assert_eq!(ParamlistParser::<Untyped>::parse(CS("foo, *args, **kwargs")), Ok((CS(""),
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

        assert_eq!(ParamlistParser::<Typed>::parse(CS("foo, *, bar, **kwargs")), Ok((CS(""),
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

        assert_eq!(ParamlistParser::<Untyped>::parse(CS("foo, *, bar, **kwargs")), Ok((CS(""),
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
}
