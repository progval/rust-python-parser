use std::marker::PhantomData;

use nom::IResult;

use ast::*;
use expressions::ExpressionParser;
use helpers::*;
use statements::{block, func_body_suite, ImportParser};

/*********************************************************************
 * Decorators
 *********************************************************************/

// decorator: '@' dotted_name [ '(' [arglist] ')' ] NEWLINE
named_args!(decorator(indent: usize) <StrSpan, Decorator>,
  do_parse!(
    indent!(indent) >>
    char!('@') >>
    name: ws_nonl!(call!(ImportParser::<NewlinesAreNotSpaces>::dotted_name)) >>
    args: opt!(ws_nonl!(delimited!(char!('('), ws_comm!(call!(ExpressionParser::<NewlinesAreSpaces>::arglist)), char!(')')))) >>
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
    s: switch!(peek!(preceded!(indent!(indent), first_word)),
        "def" => call!(funcdef, indent, decorators.clone()) // FIXME: do not clone
      | "async" => call!(funcdef, indent, decorators.clone()) // FIXME: do not clone
      | "class" => call!(classdef, indent, decorators)
    ) >> (s)
  )
);

/*********************************************************************
 * Function definition
 *********************************************************************/

// async_funcdef: 'async' funcdef
// funcdef: 'def' NAME parameters ['->' test] ':' [TYPE_COMMENT] func_body_suite
named_args!(funcdef(indent: usize, decorators: Vec<Decorator>) <StrSpan, CompoundStatement>,
  do_parse!(
    indent!(indent) >>
    async: opt!(tuple!(tag!("async"), space_sep_nonl)) >>
    tag!("def") >>
    space_sep_nonl >>
    name: name >>
    parameters: ws_nonl!(parameters) >>
    return_type: opt!(ws_nonl!(preceded!(tag!("->"), call!(ExpressionParser::<NewlinesAreNotSpaces>::test)))) >>
    ws_nonl!(char!(':')) >>
    code: call!(func_body_suite, indent) >> (
      CompoundStatement::Funcdef(Funcdef {
          async: async.is_some(), decorators, name, parameters, return_type: return_type.map(|t| *t), code
      })
    )
  )
);

// classdef: 'class' NAME ['(' [arglist] ')'] ':' suite
named_args!(classdef(indent: usize, decorators: Vec<Decorator>) <StrSpan, CompoundStatement>,
  do_parse!(
    indent!(indent) >>
    tag!("class") >>
    space_sep_nonl >>
    name: name >>
    spaces_nonl >>
    arguments: opt!(ws_nonl!(delimited!(char!('('), ws_comm!(call!(ExpressionParser::<NewlinesAreSpaces>::arglist)), char!(')')))) >>
    ws_nonl!(char!(':')) >>
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

    fn fpdef_with_default<'a>(
        i: StrSpan<'a>,
    ) -> IResult<StrSpan<'a>, (Self::Return, Option<Box<Expression>>), u32> {
        ws_comm!(
            i,
            tuple!(
                Self::fpdef,
                opt!(preceded!(
                    ws_comm!(char!('=')),
                    call!(ExpressionParser::<NewlinesAreSpaces>::test)
                ))
            )
        )
    }

    fn make_list(
        posonly_args: Vec<(Self::Return, Option<Box<Expression>>)>,
        pos_args: Vec<(Self::Return, Option<Box<Expression>>)>,
        star_args: Option<Option<Self::Return>>,
        keyword_args: Vec<(Self::Return, Option<Box<Expression>>)>,
        star_kwargs: Option<Self::Return>,
    ) -> Self::List;
}

// For typed parameter lists
struct Untyped;
impl IsItTyped for Typed {
    type Return = (Name, Option<Box<Expression>>);
    type List = TypedArgsList;

    named!(fpdef<StrSpan, Self::Return>,
      ws_comm!(tuple!(name,
        opt!(ws_comm!(preceded!(char!(':'), call!(ExpressionParser::<NewlinesAreSpaces>::test))))
      ))
    );

    fn make_list(
        posonly_args: Vec<(Self::Return, Option<Box<Expression>>)>,
        args: Vec<(Self::Return, Option<Box<Expression>>)>,
        star_args: Option<Option<Self::Return>>,
        keyword_args: Vec<(Self::Return, Option<Box<Expression>>)>,
        star_kwargs: Option<Self::Return>,
    ) -> Self::List {
        let deref_option = |o: Option<Box<_>>| o.map(|v| *v);
        TypedArgsList {
            posonly_args: posonly_args
                .into_iter()
                .map(|((name, typed), value)| (name, deref_option(typed), deref_option(value)))
                .collect(),
            args: args
                .into_iter()
                .map(|((name, typed), value)| (name, deref_option(typed), deref_option(value)))
                .collect(),
            star_args: match star_args {
                Some(Some((name, typed))) => StarParams::Named((name, deref_option(typed))),
                Some(None) => StarParams::Anonymous,
                None => StarParams::No,
            },
            keyword_args: keyword_args
                .into_iter()
                .map(|((name, typed), value)| (name, deref_option(typed), deref_option(value)))
                .collect(),
            star_kwargs: star_kwargs.map(|(name, typed)| (name, deref_option(typed))),
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

    fn make_list(
        posonly_args: Vec<(Self::Return, Option<Box<Expression>>)>,
        args: Vec<(Self::Return, Option<Box<Expression>>)>,
        star_args: Option<Option<Self::Return>>,
        keyword_args: Vec<(Self::Return, Option<Box<Expression>>)>,
        star_kwargs: Option<Self::Return>,
    ) -> Self::List {
        let deref_option = |o: Option<Box<_>>| o.map(|v| *v);
        UntypedArgsList {
            posonly_args: posonly_args
                .into_iter()
                .map(|(name, value)| (name, deref_option(value)))
                .collect(),
            args: args
                .into_iter()
                .map(|(name, value)| (name, deref_option(value)))
                .collect(),
            star_args: match star_args {
                Some(Some(name)) => StarParams::Named(name),
                Some(None) => StarParams::Anonymous,
                None => StarParams::No,
            },
            keyword_args: keyword_args
                .into_iter()
                .map(|(name, value)| (name, deref_option(value)))
                .collect(),
            star_kwargs,
        }
    }
}

// parameters: '(' [typedargslist] ')'
named!(parameters<StrSpan, TypedArgsList>,
  map!(delimited!(char!('('), opt!(ws_comm!(typedargslist)), char!(')')), |o| o.unwrap_or_default())
);

// typedargslist: (
//   (tfpdef ['=' test] (',' [TYPE_COMMENT] tfpdef ['=' test])* ',' [TYPE_COMMENT] '/' [',' [ [TYPE_COMMENT] tfpdef ['=' test] (
//         ',' [TYPE_COMMENT] tfpdef ['=' test])* (TYPE_COMMENT | [',' [TYPE_COMMENT] [
//         '*' [tfpdef] (',' [TYPE_COMMENT] tfpdef ['=' test])* (TYPE_COMMENT | [',' [TYPE_COMMENT] ['**' tfpdef [','] [TYPE_COMMENT]]])
//       | '**' tfpdef [','] [TYPE_COMMENT]]])
//   | '*' [tfpdef] (',' [TYPE_COMMENT] tfpdef ['=' test])* (TYPE_COMMENT | [',' [TYPE_COMMENT] ['**' tfpdef [','] [TYPE_COMMENT]]])
//   | '**' tfpdef [','] [TYPE_COMMENT]]] )
// |  (tfpdef ['=' test] (',' [TYPE_COMMENT] tfpdef ['=' test])* (TYPE_COMMENT | [',' [TYPE_COMMENT] [
//    '*' [tfpdef] (',' [TYPE_COMMENT] tfpdef ['=' test])* (TYPE_COMMENT | [',' [TYPE_COMMENT] ['**' tfpdef [','] [TYPE_COMMENT]]])
//   | '**' tfpdef [','] [TYPE_COMMENT]]])
//   | '*' [tfpdef] (',' [TYPE_COMMENT] tfpdef ['=' test])* (TYPE_COMMENT | [',' [TYPE_COMMENT] ['**' tfpdef [','] [TYPE_COMMENT]]])
//   | '**' tfpdef [','] [TYPE_COMMENT])
// )
//
// tfpdef: NAME [':' test]
//
// varargslist: vfpdef ['=' test ](',' vfpdef ['=' test])* ',' '/' [',' [ (vfpdef ['=' test] (',' vfpdef ['=' test])* [',' [
//         '*' [vfpdef] (',' vfpdef ['=' test])* [',' ['**' vfpdef [',']]]
//       | '**' vfpdef [',']]]
//   | '*' [vfpdef] (',' vfpdef ['=' test])* [',' ['**' vfpdef [',']]]
//   | '**' vfpdef [',']) ]] | (vfpdef ['=' test] (',' vfpdef ['=' test])* [',' [
//         '*' [vfpdef] (',' vfpdef ['=' test])* [',' ['**' vfpdef [',']]]
//       | '**' vfpdef [',']]]
//   | '*' [vfpdef] (',' vfpdef ['=' test])* [',' ['**' vfpdef [',']]]
//   | '**' vfpdef [',']
// )
//
// vfpdef: NAME
//
//
// But for legibility, we're implementing this equivalent grammar, included
// as comment in cpython's grammar:
//
// arguments = argument (',' argument )*
// argument = vfpdef ['=' test]
// kwargs = '**' vfpdef [',']
// args = '*' [vfpdef]
// kwonly_kwargs = (',' argument )* [',' [kwargs]]
// args_kwonly_kwargs = args kwonly_kwargs | kwargs
// poskeyword_args_kwonly_kwargs = arguments [',' [args_kwonly_kwargs]]
// varargslist_no_posonly = poskeyword_args_kwonly_kwargs | args_kwonly_kwargs
// varargslist = arguments ',' '/' [','[(varargslist_no_posonly)]] | (varargslist_no_posonly)
//
// with tfpdef in place of vfpdef for the typed variant.

struct ParamlistParser<IIT: IsItTyped> {
    phantom: PhantomData<IIT>,
}
impl<IIT: IsItTyped> ParamlistParser<IIT> {
    // arguments = argument (',' argument )*
    named!(arguments<StrSpan, Vec<(IIT::Return, Option<Box<Expression>>)>>,
      ws_comm!(separated_nonempty_list!(char!(','), call!(Self::argument)))
    );

    // argument = vfpdef ['=' test]
    named!(argument<StrSpan, (IIT::Return, Option<Box<Expression>>)>,
      ws_comm!(tuple!(
        call!(IIT::fpdef),
        opt!(ws_comm!(preceded!(char!('='), call!(ExpressionParser::<NewlinesAreSpaces>::test))))
      ))
    );

    // kwargs = '**' vfpdef [',']
    named!(kwargs<StrSpan, IIT::Return>,
      ws_comm!(delimited!(tag!("**"), call!(IIT::fpdef), opt!(char!(','))))
    );

    // args = '*' [vfpdef]
    named!(args<StrSpan, Option<IIT::Return>>,
      ws_comm!(preceded!(tag!("*"), opt!(call!(IIT::fpdef))))
    );

    // kwonly_kwargs = (',' argument )* [',' [kwargs]]
    // returns (vec![kwonly_argument], kwargs)
    named!(kwonly_kwargs<StrSpan, (Vec<(IIT::Return, Option<Box<Expression>>)>, Option<IIT::Return>)>,
      do_parse!(
        arguments: ws_comm!(many0!(preceded!(char!(','), call!(Self::argument)))) >>
        kwargs: opt!(ws_comm!(preceded!(char!(','), opt!(Self::kwargs)))) >> (
          (arguments, kwargs.flatten())
        )
      )
    );

    // args_kwonly_kwargs = args kwonly_kwargs | kwargs
    // returns (args, vec![kwonly_argument], kwargs)
    named!(args_kwonly_kwargs<StrSpan, (Option<Option<IIT::Return>>, Vec<(IIT::Return, Option<Box<Expression>>)>, Option<IIT::Return>)>,
      alt!(
        call!(Self::kwargs) => {|kwargs| (None, Vec::new(), Option::Some(kwargs))}
      | do_parse!(
          args: call!(Self::args) >>
          kwonly_kwargs: call!(Self::kwonly_kwargs) >> ({
            let (arguments, kwargs) = kwonly_kwargs;
            (Option::Some(args), arguments, kwargs)
          })
        )
      )
    );

    // poskeyword_args_kwonly_kwargs = arguments [',' [args_kwonly_kwargs]]
    // returns (vec![argument], args, vec![kwonly_argument], kwargs)
    named!(poskeyword_args_kwonly_kwargs<StrSpan, (Vec<(IIT::Return, Option<Box<Expression>>)>, Option<Option<IIT::Return>>, Vec<(IIT::Return, Option<Box<Expression>>)>, Option<IIT::Return>)>,
      do_parse!(
        arguments: call!(Self::arguments) >>
        rest: opt!(ws_comm!(preceded!(char!(','), opt!(call!(Self::args_kwonly_kwargs))))) >> ({
          if let Some(Some((args, kwonly_arguments, kwargs))) = rest {
            (arguments, args, kwonly_arguments, kwargs)
          }
          else {
            (arguments, None, Vec::new(), None)
          }
        })
      )
    );

    // varargslist_no_posonly = poskeyword_args_kwonly_kwargs | args_kwonly_kwargs
    // returns (vec![argument], args, vec![kwonly_argument], kwargs)
    named!(varargslist_no_posonly<StrSpan, (Vec<(IIT::Return, Option<Box<Expression>>)>, Option<Option<IIT::Return>>, Vec<(IIT::Return, Option<Box<Expression>>)>, Option<IIT::Return>)>,
      alt!(
        call!(Self::poskeyword_args_kwonly_kwargs)
      | call!(Self::args_kwonly_kwargs) => {|(args, kwonly_arguments, kwargs)|
          (Vec::new(), args, kwonly_arguments, kwargs)
        }
      )
    );

    // varargslist = arguments ',' '/' [','[(varargslist_no_posonly)]] | (varargslist_no_posonly)
    // returns (vec![posonly_argument], vec![argument], args, vec![kwonly_argument], kwargs)
    named!(varargslist<StrSpan, (Vec<(IIT::Return, Option<Box<Expression>>)>, Vec<(IIT::Return, Option<Box<Expression>>)>, Option<Option<IIT::Return>>, Vec<(IIT::Return, Option<Box<Expression>>)>, Option<IIT::Return>)>,
      alt!(
        ws_comm!(do_parse!(
          posonly_arguments: ws_comm!(call!(Self::arguments)) >>
          char!(',') >>
          char!('/') >>
          varargslist_no_posonly: opt!(ws_comm!(preceded!(char!(','), opt!(call!(Self::varargslist_no_posonly))))) >> ({
            if let Some(Some((arguments, args, kwonly_arguments, kwargs))) = varargslist_no_posonly {
                (posonly_arguments, arguments, args, kwonly_arguments, kwargs)
            }
            else {
                (posonly_arguments, Vec::new(), None, Vec::new(), None)
            }
          })
        ))
      | call!(Self::varargslist_no_posonly) => {|varargslist_no_posonly| {
            let (arguments, args, kwonly_arguments, kwargs) = varargslist_no_posonly;
            (Vec::new(), arguments, args, kwonly_arguments, kwargs)
        }}
      )
    );



    named!(parse<StrSpan, IIT::List>,
      map!(call!(Self::varargslist), |varargslist| {
        let (posonly_arguments, arguments, args, kwonly_arguments, kwargs) = varargslist;
        IIT::make_list(posonly_arguments, arguments, args, kwonly_arguments, kwargs)
      })
    );
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
    use helpers::{assert_parse_eq, make_strspan};

    #[test]
    fn test_decorator() {
        assert_parse_eq(
            decorator(make_strspan("@foo\n"), 0),
            Ok((
                make_strspan(""),
                Decorator {
                    name: vec!["foo".to_string()],
                    args: None,
                },
            )),
        );
        assert_parse_eq(
            decorator(make_strspan("@foo.bar\n"), 0),
            Ok((
                make_strspan(""),
                Decorator {
                    name: vec!["foo".to_string(), "bar".to_string()],
                    args: None,
                },
            )),
        );

        assert_parse_eq(
            decorator(make_strspan("@foo(baz)\n"), 0),
            Ok((
                make_strspan(""),
                Decorator {
                    name: vec!["foo".to_string()],
                    args: Some(vec![Argument::Positional(Expression::Name(
                        "baz".to_string(),
                    ))]),
                },
            )),
        );
        assert_parse_eq(
            decorator(make_strspan("@foo.bar(baz)\n"), 0),
            Ok((
                make_strspan(""),
                Decorator {
                    name: vec!["foo".to_string(), "bar".to_string()],
                    args: Some(vec![Argument::Positional(Expression::Name(
                        "baz".to_string(),
                    ))]),
                },
            )),
        );
        assert_parse_eq(
            decorator(make_strspan("  @foo.bar(baz)\n"), 2),
            Ok((
                make_strspan(""),
                Decorator {
                    name: vec!["foo".to_string(), "bar".to_string()],
                    args: Some(vec![Argument::Positional(Expression::Name(
                        "baz".to_string(),
                    ))]),
                },
            )),
        );
    }

    #[test]
    fn test_funcdef() {
        assert_parse_eq(
            decorated(make_strspan("def foo():\n bar"), 0),
            Ok((
                make_strspan(""),
                CompoundStatement::Funcdef(Funcdef {
                    async: false,
                    decorators: vec![],
                    name: "foo".to_string(),
                    parameters: TypedArgsList::default(),
                    return_type: None,
                    code: vec![Statement::Assignment(
                        vec![Expression::Name("bar".to_string())],
                        vec![],
                    )],
                }),
            )),
        );

        assert_parse_eq(
            decorated(make_strspan(" def foo():\n  bar"), 1),
            Ok((
                make_strspan(""),
                CompoundStatement::Funcdef(Funcdef {
                    async: false,
                    decorators: vec![],
                    name: "foo".to_string(),
                    parameters: TypedArgsList::default(),
                    return_type: None,
                    code: vec![Statement::Assignment(
                        vec![Expression::Name("bar".to_string())],
                        vec![],
                    )],
                }),
            )),
        );

        assert!(decorated(make_strspan(" def foo():\n bar"), 1).is_err());
    }

    #[test]
    fn test_decorated_func() {
        assert_parse_eq(
            decorated(make_strspan(" @foo\n def foo():\n  bar"), 1),
            Ok((
                make_strspan(""),
                CompoundStatement::Funcdef(Funcdef {
                    async: false,
                    decorators: vec![Decorator {
                        name: vec!["foo".to_string()],
                        args: None,
                    }],
                    name: "foo".to_string(),
                    parameters: TypedArgsList::default(),
                    return_type: None,
                    code: vec![Statement::Assignment(
                        vec![Expression::Name("bar".to_string())],
                        vec![],
                    )],
                }),
            )),
        );
    }

    #[test]
    fn test_positional() {
        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None, None)],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None)],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo=bar")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![],
                    args: vec![(
                        "foo".to_string(),
                        None,
                        Some(Expression::Name("bar".to_string())),
                    )],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo=bar")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![],
                    args: vec![(
                        "foo".to_string(),
                        Some(Expression::Name("bar".to_string())),
                    )],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo = bar")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![],
                    args: vec![(
                        "foo".to_string(),
                        None,
                        Some(Expression::Name("bar".to_string())),
                    )],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo = bar")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![],
                    args: vec![(
                        "foo".to_string(),
                        Some(Expression::Name("bar".to_string())),
                    )],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo:bar")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![],
                    args: vec![(
                        "foo".to_string(),
                        Some(Expression::Name("bar".to_string())),
                        None,
                    )],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo : bar")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![],
                    args: vec![(
                        "foo".to_string(),
                        Some(Expression::Name("bar".to_string())),
                        None,
                    )],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo:bar")),
            Ok((
                make_strspan(":bar"),
                UntypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None)],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo:bar=baz")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![],
                    args: vec![(
                        "foo".to_string(),
                        Some(Expression::Name("bar".to_string())),
                        Some(Expression::Name("baz".to_string())),
                    )],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo : bar = baz")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![],
                    args: vec![(
                        "foo".to_string(),
                        Some(Expression::Name("bar".to_string())),
                        Some(Expression::Name("baz".to_string())),
                    )],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo:bar=baz")),
            Ok((
                make_strspan(":bar=baz"),
                UntypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None)],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo, bar")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![],
                    args: vec![
                        ("foo".to_string(), None, None),
                        ("bar".to_string(), None, None),
                    ],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo, bar")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None), ("bar".to_string(), None)],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );
    }

    #[test]
    fn test_star_args() {
        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo, *, bar")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None, None)],
                    star_args: StarParams::Anonymous,
                    keyword_args: vec![("bar".to_string(), None, None)],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo, *, bar")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None)],
                    star_args: StarParams::Anonymous,
                    keyword_args: vec![("bar".to_string(), None)],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo, *, bar=baz")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None, None)],
                    star_args: StarParams::Anonymous,
                    keyword_args: vec![(
                        "bar".to_string(),
                        None,
                        Some(Expression::Name("baz".to_string())),
                    )],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo, *, bar=baz")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None)],
                    star_args: StarParams::Anonymous,
                    keyword_args: vec![(
                        "bar".to_string(),
                        Some(Expression::Name("baz".to_string())),
                    )],
                    star_kwargs: None,
                },
            )),
        );
    }

    #[test]
    fn test_star_kwargs() {
        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo, **kwargs")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None, None)],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: Some(("kwargs".to_string(), None)),
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo, **kwargs")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None)],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: Some("kwargs".to_string()),
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo, *args, **kwargs")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None, None)],
                    star_args: StarParams::Named(("args".to_string(), None)),
                    keyword_args: vec![],
                    star_kwargs: Some(("kwargs".to_string(), None)),
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo, *args, **kwargs")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None)],
                    star_args: StarParams::Named("args".to_string()),
                    keyword_args: vec![],
                    star_kwargs: Some("kwargs".to_string()),
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo, *, bar, **kwargs")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None, None)],
                    star_args: StarParams::Anonymous,
                    keyword_args: vec![("bar".to_string(), None, None)],
                    star_kwargs: Some(("kwargs".to_string(), None)),
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo, *, bar, **kwargs")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![],
                    args: vec![("foo".to_string(), None)],
                    star_args: StarParams::Anonymous,
                    keyword_args: vec![("bar".to_string(), None)],
                    star_kwargs: Some("kwargs".to_string()),
                },
            )),
        );
    }

    #[test]
    fn test_starargs_first() {
        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("*foo, bar, **kwargs")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![],
                    args: vec![],
                    star_args: StarParams::Named("foo".to_string()),
                    keyword_args: vec![("bar".to_string(), None)],
                    star_kwargs: Some("kwargs".to_string()),
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("*foo, **kwargs")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![],
                    args: vec![],
                    star_args: StarParams::Named("foo".to_string()),
                    keyword_args: vec![],
                    star_kwargs: Some("kwargs".to_string()),
                },
            )),
        );
    }

    #[test]
    fn test_posonly_args() {
        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo, /, bar")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![("foo".to_string(), None, None)],
                    args: vec![("bar".to_string(), None, None)],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo, /, bar")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![("foo".to_string(), None)],
                    args: vec![("bar".to_string(), None)],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo, /, bar=baz")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![("foo".to_string(), None, None)],
                    args: vec![(
                        "bar".to_string(),
                        None,
                        Some(Expression::Name("baz".to_string())),
                    )],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo, /, bar=baz")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![("foo".to_string(), None)],
                    args: vec![(
                        "bar".to_string(),
                        Some(Expression::Name("baz".to_string())),
                    )],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: None,
                },
            )),
        );
    }

    #[test]
    fn test_posonly_args_star_args() {
        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo, /, *, bar")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![("foo".to_string(), None, None)],
                    args: vec![],
                    star_args: StarParams::Anonymous,
                    keyword_args: vec![("bar".to_string(), None, None)],
                    star_kwargs: None,
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo, /, *, bar")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![("foo".to_string(), None)],
                    args: vec![],
                    star_args: StarParams::Anonymous,
                    keyword_args: vec![("bar".to_string(), None)],
                    star_kwargs: None,
                },
            )),
        );
    }

    #[test]
    fn test_posonly_args_star_kwargs() {
        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo, /, **kwargs")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![("foo".to_string(), None, None)],
                    args: vec![],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: Some(("kwargs".to_string(), None)),
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo, /, **kwargs")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![("foo".to_string(), None)],
                    args: vec![],
                    star_args: StarParams::No,
                    keyword_args: vec![],
                    star_kwargs: Some("kwargs".to_string()),
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo, /, *args, **kwargs")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![("foo".to_string(), None, None)],
                    args: vec![],
                    star_args: StarParams::Named(("args".to_string(), None)),
                    keyword_args: vec![],
                    star_kwargs: Some(("kwargs".to_string(), None)),
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo, /, *args, **kwargs")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![("foo".to_string(), None)],
                    args: vec![],
                    star_args: StarParams::Named("args".to_string()),
                    keyword_args: vec![],
                    star_kwargs: Some("kwargs".to_string()),
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Typed>::parse(make_strspan("foo, /, *, bar, **kwargs")),
            Ok((
                make_strspan(""),
                TypedArgsList {
                    posonly_args: vec![("foo".to_string(), None, None)],
                    args: vec![],
                    star_args: StarParams::Anonymous,
                    keyword_args: vec![("bar".to_string(), None, None)],
                    star_kwargs: Some(("kwargs".to_string(), None)),
                },
            )),
        );

        assert_parse_eq(
            ParamlistParser::<Untyped>::parse(make_strspan("foo, /, *, bar, **kwargs")),
            Ok((
                make_strspan(""),
                UntypedArgsList {
                    posonly_args: vec![("foo".to_string(), None)],
                    args: vec![],
                    star_args: StarParams::Anonymous,
                    keyword_args: vec![("bar".to_string(), None)],
                    star_kwargs: Some("kwargs".to_string()),
                },
            )),
        );
    }
}
