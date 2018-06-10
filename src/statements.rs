use std::marker::PhantomData;

use helpers::*;
use expressions::ExpressionParser;
use functions::decorated;
use ast::*;


macro_rules! call_test {
    ( $i:expr, $($args:tt)* ) => { call!($i, ExpressionParser::<NewlinesAreNotSpaces>::test, $($args)*) }
}

/*********************************************************************
 * Base statement parsers
 *********************************************************************/

// stmt: simple_stmt | compound_stmt
named_args!(pub statement(indent: usize) <StrSpan, Vec<Statement>>,
  alt!(
    call!(compound_stmt, indent) => { |stmt| vec![Statement::Compound(Box::new(stmt))] }
  | preceded!(count!(char!(' '), indent), call!(simple_stmt))
  )
);

// simple_stmt: small_stmt (';' small_stmt)* [';'] NEWLINE
named_args!(simple_stmt() <StrSpan, Vec<Statement>>,
  do_parse!(
    stmts: separated_nonempty_list!(ws2!(semicolon), call!(small_stmt)) >>
    opt!(semicolon) >> (
      stmts
    )
  )
);

// small_stmt: (expr_stmt | del_stmt | pass_stmt | flow_stmt |
//             import_stmt | global_stmt | nonlocal_stmt | assert_stmt)
named!(small_stmt<StrSpan, Statement>,
  alt!(
    del_stmt
  | pass_stmt
  | flow_stmt
  | import_stmt
  | global_stmt
  | nonlocal_stmt
  | assert_stmt
  | expr_stmt
  )
);

/*********************************************************************
 * Expression statements
 *********************************************************************/

// expr_stmt: testlist_star_expr (annassign | augassign (yield_expr|testlist) |
//                     ('=' (yield_expr|testlist_star_expr))*)
// annassign: ':' test ['=' test]
named!(expr_stmt<StrSpan, Statement>,
  do_parse!(
    lhs: testlist_star_expr >>
    r: ws2!(alt!(
      // Case 1: "foo: bar = baz"
      do_parse!(
        char!(':') >>
        typed: call!(ExpressionParser::<NewlinesAreNotSpaces>::test) >>
        char!('=') >>
        rhs: call!(ExpressionParser::<NewlinesAreNotSpaces>::test) >> (
          Statement::TypedAssignment(lhs.clone(), *typed, vec![*rhs])
        )
      )

    | // Case 2: "Foo += bar" (and other operators)
      do_parse!(
        op: augassign >>
        rhs: alt!(
          call!(ExpressionParser::<NewlinesAreNotSpaces>::yield_expr) => { |e| vec![e] }
        | call!(ExpressionParser::<NewlinesAreNotSpaces>::testlist)
        ) >> (
          Statement::AugmentedAssignment(lhs.clone(), op, rhs)
        )
      )

    | // Case 3: "foo", "foo = bar", "foo = bar = baz", ...
      do_parse!(
        rhs: many0!(ws2!(preceded!(char!('='), alt!(
          call!(ExpressionParser::<NewlinesAreNotSpaces>::yield_expr) => { |e| vec![e] }
        | testlist_star_expr
        )))) >> (
          Statement::Assignment(lhs, rhs)
        )
      )
    )) >>
    (r)
  )
);

// testlist_star_expr: (test|star_expr) (',' (test|star_expr))* [',']
named!(testlist_star_expr<StrSpan, Vec<Expression>>,
  terminated!(
    separated_nonempty_list!(
      ws2!(char!(',')),
      map!(alt!(
        call!(ExpressionParser::<NewlinesAreNotSpaces>::test)
      | call!(ExpressionParser::<NewlinesAreNotSpaces>::star_expr)
      ), |e| *e)
    ),
    opt!(ws2!(char!(',')))
  )
);

// augassign: ('+=' | '-=' | '*=' | '@=' | '/=' | '%=' | '&=' | '|=' | '^=' |
//            '<<=' | '>>=' | '**=' | '//=')
named!(augassign<StrSpan, AugAssignOp>,
  ws2!(alt!(
    tag!("+=") => { |_| AugAssignOp::Add }
  | tag!("-=") => { |_| AugAssignOp::Sub }
  | tag!("*=") => { |_| AugAssignOp::Mult }
  | tag!("@=") => { |_| AugAssignOp::MatMult }
  | tag!("/=") => { |_| AugAssignOp::Div }
  | tag!("%=") => { |_| AugAssignOp::Mod }
  | tag!("&=") => { |_| AugAssignOp::BitAnd }
  | tag!("|=") => { |_| AugAssignOp::BitOr }
  | tag!("^=") => { |_| AugAssignOp::BitXor }
  | tag!("<<=") => { |_| AugAssignOp::Lshift }
  | tag!(">>=") => { |_| AugAssignOp::Rshift }
  | tag!("**=") => { |_| AugAssignOp::Power }
  | tag!("//=") => { |_| AugAssignOp::Floordiv }
  ))
);

/*********************************************************************
 * Small statements
 *********************************************************************/

// del_stmt: 'del' exprlist
named!(del_stmt<StrSpan, Statement>,
  map!(preceded!(tuple!(tag!("del"), space_sep2), ExpressionParser::<NewlinesAreNotSpaces>::exprlist), |v:Vec<_>| Statement::Del(v))
  // TODO: check it's one of the allowed form of del expression
);

// pass_stmt: 'pass'
named!(pass_stmt<StrSpan, Statement>,
  map!(tag!("pass"), |_| Statement::Pass)
);

// flow_stmt: break_stmt | continue_stmt | return_stmt | raise_stmt | yield_stmt
// break_stmt: 'break'
// continue_stmt: 'continue'
// return_stmt: 'return' [testlist]
// yield_stmt: yield_expr
named!(flow_stmt<StrSpan, Statement>,
  alt!(
    tag!("break") => { |_| Statement::Break }
  | tag!("continue") => { |_| Statement::Continue }
  | preceded!(
      tuple!(tag!("return"), space_sep2),
      ws2!(call!(ExpressionParser::<NewlinesAreNotSpaces>::possibly_empty_testlist))
    ) => { |e| Statement::Return(e) }
  | raise_stmt
  | call!(ExpressionParser::<NewlinesAreNotSpaces>::yield_expr)
    => { |e| Statement::Expressions(vec![e]) }
  )
);

// raise_stmt: 'raise' [test ['from' test]]
named!(raise_stmt<StrSpan, Statement>,
  do_parse!(
    tag!("raise") >>
    t: opt!(tuple!(
      preceded!(spaces2, call_test!()),
      opt!(preceded!(ws2!(tag!("from")), call_test!()))
    )) >> (
      match t {
        Some((exc, Some(from_exc))) => Statement::RaiseExcFrom(*exc, *from_exc),
        Some((exc, None)) => Statement::RaiseExc(*exc),
        None => Statement::Raise,
      }
    )
  )
);

// global_stmt: 'global' NAME (',' NAME)*
named!(global_stmt<StrSpan, Statement>,
  map!(preceded!(tuple!(tag!("global"), space_sep2),
    ws2!(separated_nonempty_list!(ws2!(char!(',')), name))
  ), |names| Statement::Global(names))
);

// nonlocal_stmt: 'nonlocal' NAME (',' NAME)*
named!(nonlocal_stmt<StrSpan, Statement>,
  map!(preceded!(tuple!(tag!("nonlocal"), space_sep2),
    ws2!(separated_nonempty_list!(ws2!(char!(',')), name))
  ), |names| Statement::Nonlocal(names))
);

// assert_stmt: 'assert' test [',' test]
named!(assert_stmt<StrSpan, Statement>,
  do_parse!(
    tag!("assert") >>
    space_sep2 >>
    assertion: call_test!() >>
    msg: opt!(preceded!(ws2!(char!(',')), call_test!())) >> (
      Statement::Assert(*assertion, msg.map(|m| *m))
    )
  )
);

/*********************************************************************
 * Imports
 *********************************************************************/

// import_stmt: import_name | import_from
named!(import_stmt<StrSpan, Statement>,
  alt!(
    import_name => { |i| Statement::Import(i) }
  | import_from => { |i| Statement::Import(i) }
  )
);

// import_name: 'import' dotted_as_names
named!(import_name<StrSpan, Import>,
  map!(preceded!(tuple!(tag!("import"), space_sep2), call!(ImportParser::<NewlinesAreNotSpaces>::dotted_as_names)),
    |names| Import::Import { names }
  )
);

// import_from: ('from' (('.' | '...')* dotted_name | ('.' | '...')+)
//               'import' ('*' | '(' import_as_names ')' | import_as_names))
//
// the explicit presence of '...' is for parsers that use a lexer, because
// they would recognize ... as an ellipsis.
named!(import_from<StrSpan, Import>,
  do_parse!(
    tag!("from") >>
    space_sep2 >>
    import_from: alt!(
      preceded!(char!('.'), do_parse!(
        leading_dots: ws2!(map!(many0!(char!('.')), |dots| dots.len()+1)) >>
        from_name: opt!(call!(ImportParser::<NewlinesAreNotSpaces>::dotted_name)) >> (
          (leading_dots, from_name.unwrap_or(Vec::new()))
        )
      ))
    | call!(ImportParser::<NewlinesAreNotSpaces>::dotted_name) => { |n| (0, n) }
    ) >>
    space_sep2 >>
    tag!("import") >>
    space_sep2 >>
    names: alt!(
      char!('*') => { |_| Vec::new() }
    | ws2!(delimited!(char!('('), call!(ImportParser::<NewlinesAreSpaces>::import_as_names), char!(')')))
    | call!(ImportParser::<NewlinesAreNotSpaces>::import_as_names)
    ) >> ({
      let (leading_dots, path) = import_from;
      if names.len() > 0 {
          Import::ImportFrom { leading_dots, path, names }
      }
      else {
          Import::ImportStarFrom { leading_dots, path }
      }
    })
  )
);

pub(crate) struct ImportParser<ANS: AreNewlinesSpaces> {
    _phantom: PhantomData<ANS>,
}

impl<ANS: AreNewlinesSpaces> ImportParser<ANS> {

// import_as_name: NAME ['as' NAME]
named!(import_as_name<StrSpan, (Name, Option<Name>)>,
  tuple!(name, opt!(do_parse!(
    space_sep!() >>
    tag!("as") >>
    space_sep!() >>
    name: name >> (
      name
    )
  )))
);

// dotted_as_name: dotted_name ['as' NAME]
named!(dotted_as_name<StrSpan, (Vec<Name>, Option<Name>)>,
  tuple!(call!(Self::dotted_name), opt!(do_parse!(
    space_sep!() >>
    tag!("as") >>
    space_sep!() >>
    name: name >> (
      name
    )
  )))
);

// import_as_names: import_as_name (',' import_as_name)* [',']
named!(import_as_names<StrSpan, Vec<(Name, Option<Name>)>>,
  ws3!(terminated!(
    separated_nonempty_list!(ws3!(char!(',')), call!(Self::import_as_name)),
    opt!(ws3!(char!(',')))
  ))
);

// dotted_as_names: dotted_as_name (',' dotted_as_name)*
named!(dotted_as_names<StrSpan, Vec<(Vec<Name>, Option<Name>)>>,
  separated_nonempty_list!(ws2!(char!(',')), call!(Self::dotted_as_name))
);

// dotted_name: NAME ('.' NAME)*
named!(pub dotted_name<StrSpan, Vec<Name>>,
  separated_nonempty_list!(ws2!(char!('.')), name)
);

} // end ImportParser

/*********************************************************************
 * Blocks
 *********************************************************************/

// suite: simple_stmt | NEWLINE INDENT stmt+ DEDENT
named_args!(pub block(indent: usize) <StrSpan, Vec<Statement>>,
  alt!(
    do_parse!(
      new_indent: peek!(
        do_parse!(
          newline >>
          count!(char!(' '), indent) >>
          new_spaces: many1!(char!(' ')) >> ({
            indent + new_spaces.len()
          })
        )
      ) >>
      stmts: fold_many1!(
        do_parse!(
          newline >>
          r: call!(statement, new_indent) >>
          (r)
        ),
        Vec::new(),
        |mut acc: Vec<_>, stmt| { acc.extend(stmt); acc }
      ) >>
      (stmts)
    )
  | call!(simple_stmt)
  )
);
named_args!(cond_and_block(indent: usize) <StrSpan, (Expression, Vec<Statement>)>,
  do_parse!(
    spaces >>
    cond: call!(ExpressionParser::<NewlinesAreNotSpaces>::test) >>
    ws2!(char!(':')) >>
    block: call!(block, indent) >> (
      (*cond, block)
    )
  )
);


// compound_stmt: if_stmt | while_stmt | for_stmt | try_stmt | with_stmt | funcdef | classdef | decorated | async_stmt
named_args!(compound_stmt(indent: usize) <StrSpan, CompoundStatement>,
  switch!(map!(peek!(ws2!(take!(1))), |s| s.fragment.0),
    "i" => call!(if_stmt, indent)
  | "f" => call!(for_stmt, indent)
  | "w" => alt!(
      call!(while_stmt, indent)
    | call!(with_stmt, indent)
    )
  | "t" => call!(try_stmt, indent)
  | "d" => call!(decorated, indent)
  | "c" => call!(decorated, indent)
  | "a" => alt!(
      call!(decorated, indent) // ASYNC funcdef
    | call!(for_stmt, indent)
    )
  | "@" => call!(decorated, indent)
  )
);

// async_stmt: ASYNC (funcdef | with_stmt | for_stmt)
// taken care of in other parsers

named_args!(else_block(indent: usize) <StrSpan, Option<Vec<Statement>>>,
  opt!(
    preceded!(
      tuple!(newline, count!(char!(' '), indent), tag!("else"), ws2!(char!(':'))),
      call!(block, indent)
    )
  )
);

// if_stmt: 'if' test ':' suite ('elif' test ':' suite)* ['else' ':' suite]
named_args!(if_stmt(indent: usize) <StrSpan, CompoundStatement>,
  do_parse!(
    count!(char!(' '), indent) >>
    tag!("if") >>
    if_block: call!(cond_and_block, indent) >>
    elif_blocks: many0!(
      preceded!(
        tuple!(newline, count!(char!(' '), indent), tag!("elif")),
        call!(cond_and_block, indent)
      )
    ) >>
    else_block: call!(else_block, indent) >> ({
      let mut blocks: Vec<_> = elif_blocks;
      blocks.insert(0, if_block);
      CompoundStatement::If(blocks, else_block)
    })
  )
);

// while_stmt: 'while' test ':' suite ['else' ':' suite]
named_args!(while_stmt(indent: usize) <StrSpan, CompoundStatement>,
  do_parse!(
    count!(char!(' '), indent) >>
    tag!("while") >>
    while_block: call!(cond_and_block, indent) >>
    else_block: call!(else_block, indent) >> ({
      let (cond, while_block) = while_block;
      CompoundStatement::While(cond, while_block, else_block)
    })
  )
);

// for_stmt: 'for' exprlist 'in' testlist ':' suite ['else' ':' suite]
named_args!(for_stmt(indent: usize) <StrSpan, CompoundStatement>,
  do_parse!(
    count!(char!(' '), indent) >>
    async: opt!(tuple!(tag!("async"), space_sep2)) >>
    tag!("for") >>
    spaces >>
    item: call!(ExpressionParser::<NewlinesAreNotSpaces>::exprlist) >>
    ws2!(tag!("in")) >>
    iterator: call!(ExpressionParser::<NewlinesAreNotSpaces>::exprlist) >>
    spaces >>
    ws2!(char!(':')) >>
    for_block: call!(block, indent) >>
    else_block: call!(else_block, indent) >> ({
      CompoundStatement::For {
          async: async.is_some(),
          item, iterator, for_block, else_block
      }
    })
  )
);

// try_stmt: ('try' ':' suite
//            ((except_clause ':' suite)+
//             ['else' ':' suite]
//             ['finally' ':' suite] |
//             'finally' ':' suite))
// except_clause: 'except' [test ['as' NAME]]
named_args!(try_stmt(indent: usize) <StrSpan, CompoundStatement>,
  do_parse!(
    count!(char!(' '), indent) >>
    tag!("try") >>
    ws2!(char!(':')) >>
    try_block: call!(block, indent) >>
    except_clauses: many0!(do_parse!(
      newline >>
      count!(char!(' '), indent) >> 
      tag!("except") >>
      spaces >>
      catch_what: call!(ExpressionParser::<NewlinesAreNotSpaces>::test) >>
      spaces >>
      catch_as: opt!(preceded!(tuple!(tag!("as"), space_sep2), name)) >>
      ws2!(char!(':')) >>
      block: call!(block, indent) >> (
        (*catch_what, catch_as, block)
      )
    )) >>
    last_except: opt!(do_parse!( 
      newline >>
      count!(char!(' '), indent) >>
      tag!("except") >>
      ws2!(char!(':')) >>
      r: call!(block, indent) >>
      (r)
    )) >>
    else_block: opt!(do_parse!( 
      newline >>
      count!(char!(' '), indent) >>
      tag!("else") >>
      ws2!(char!(':')) >>
      r: call!(block, indent) >>
      (r)
    )) >>
    finally_block: opt!(do_parse!( 
      newline >>
      count!(char!(' '), indent) >>
      tag!("finally") >>
      ws2!(char!(':')) >>
      r: call!(block, indent) >>
      (r)
    )) >> (
      CompoundStatement::Try(Try {
          try_block, except_clauses,
          last_except: last_except.unwrap_or_default(),
          else_block: else_block.unwrap_or_default(),
          finally_block: finally_block.unwrap_or_default()
      })
    )
  )
);

// with_stmt: 'with' with_item (',' with_item)*  ':' suite
// with_item: test ['as' expr]
named_args!(with_stmt(indent: usize) <StrSpan, CompoundStatement>,
  do_parse!(
    count!(char!(' '), indent) >>
    tag!("with") >>
    spaces2 >>
    contexts: separated_nonempty_list!(ws2!(char!(',')), do_parse!(
      context: call!(ExpressionParser::<NewlinesAreNotSpaces>::expr) >>
      as_: opt!(preceded!(
        ws2!(tag!("as")), 
        call!(ExpressionParser::<NewlinesAreNotSpaces>::expr)
      )) >> (
        (*context, as_.map(|e| *e))
      )
    )) >>
    ws2!(char!(':')) >>
    code: call!(block, indent) >> (
      CompoundStatement::With(contexts, code)
    )
  )
);



    

/*********************************************************************
 * Unit tests
 *********************************************************************/

#[cfg(test)]
mod tests {
    use super::*;
    use helpers::{make_strspan, assert_parse_eq};

    #[test]
    fn test_statement_indent() {
        assert_parse_eq(statement(make_strspan("del foo"), 0), Ok((make_strspan(""), vec![Statement::Del(vec![Expression::Name("foo".to_string())])])));
        assert_parse_eq(statement(make_strspan(" del foo"), 1), Ok((make_strspan(""), vec![Statement::Del(vec![Expression::Name("foo".to_string())])])));
        assert!(statement(make_strspan(" del foo"), 0).is_err());
        assert!(statement(make_strspan("  del foo"), 1).is_err());
        assert!(statement(make_strspan("del foo"), 1).is_err());
    }

    #[test]
    fn test_block() {
        assert_parse_eq(block(make_strspan("\n del foo"), 0), Ok((make_strspan(""), vec![Statement::Del(vec![Expression::Name("foo".to_string())])])));
        assert_parse_eq(block(make_strspan("\n  del foo"), 1), Ok((make_strspan(""), vec![Statement::Del(vec![Expression::Name("foo".to_string())])])));
        assert_parse_eq(block(make_strspan("\n      del foo"), 1), Ok((make_strspan(""), vec![Statement::Del(vec![Expression::Name("foo".to_string())])])));
        assert!(block(make_strspan("\ndel foo"), 0).is_err());
        assert!(block(make_strspan("\ndel foo"), 1).is_err());
        assert!(block(make_strspan("\n del foo"), 1).is_err());

        assert_parse_eq(block(make_strspan("\n del foo\n del foo"), 0), Ok((make_strspan(""), vec![Statement::Del(vec![Expression::Name("foo".to_string())]), Statement::Del(vec![Expression::Name("foo".to_string())])])));
        assert_parse_eq(block(make_strspan("\n  del foo\n  del foo"), 1), Ok((make_strspan(""), vec![Statement::Del(vec![Expression::Name("foo".to_string())]), Statement::Del(vec![Expression::Name("foo".to_string())])])));
        assert_parse_eq(block(make_strspan("\n      del foo\n      del foo"), 1), Ok((make_strspan(""), vec![Statement::Del(vec![Expression::Name("foo".to_string())]), Statement::Del(vec![Expression::Name("foo".to_string())])])));
        assert_parse_eq(block(make_strspan("\n del foo\ndel foo"), 0), Ok((make_strspan("\ndel foo"), vec![Statement::Del(vec![Expression::Name("foo".to_string())])])));
        assert_parse_eq(block(make_strspan("\n del foo\n  del foo"), 0), Ok((make_strspan("\n  del foo"), vec![Statement::Del(vec![Expression::Name("foo".to_string())])])));
    }

    #[test]
    fn test_del() {
        assert_parse_eq(statement(make_strspan("del foo"), 0), Ok((make_strspan(""),
            vec![
                Statement::Del(vec![Expression::Name("foo".to_string())]),
            ]
        )));

        assert_parse_eq(statement(make_strspan("del foo, bar"), 0), Ok((make_strspan(""),
            vec![
                Statement::Del(vec![
                    Expression::Name("foo".to_string()),
                    Expression::Name("bar".to_string())
                ]),
            ]
        )));
    }

    #[test]
    fn test_assert1() {
        assert_parse_eq(block(make_strspan("assert foo"), 0), Ok((make_strspan(""),
            vec![
                Statement::Assert(
                    Expression::Name("foo".to_string()),
                    None
                ),
            ]
        )));
    }

    #[test]
    fn test_assert2() {
        assert_parse_eq(block(make_strspan("assert foo and bar"), 0), Ok((make_strspan(""),
            vec![
                Statement::Assert(
                    Expression::Bop(Bop::And,
                        Box::new(Expression::Name("foo".to_string())),
                        Box::new(Expression::Name("bar".to_string())),
                    ),
                    None
                ),
            ]
        )));
    }

    #[test]
    fn test_assert3() {
        assert_parse_eq(block(make_strspan("assert (foo and bar)"), 0), Ok((make_strspan(""),
            vec![
                Statement::Assert(
                    Expression::Bop(Bop::And,
                        Box::new(Expression::Name("foo".to_string())),
                        Box::new(Expression::Name("bar".to_string())),
                    ),
                    None
                ),
            ]
        )));
    }

    #[test]
    fn test_assert4() {
        assert_parse_eq(block(make_strspan("assert (foo and\n bar)"), 0), Ok((make_strspan(""),
            vec![
                Statement::Assert(
                    Expression::Bop(Bop::And,
                        Box::new(Expression::Name("foo".to_string())),
                        Box::new(Expression::Name("bar".to_string())),
                    ),
                    None
                ),
            ]
        )));
    }

    #[test]
    fn test_if() {
        assert_parse_eq(compound_stmt(make_strspan("if foo:\n del bar"), 0), Ok((make_strspan(""),
            CompoundStatement::If(
                vec![
                    (
                        Expression::Name("foo".to_string()),
                        vec![
                            Statement::Del(vec![Expression::Name("bar".to_string())])
                        ]
                    ),
                ],
                None
            )
        )));
    }

    #[test]
    fn test_elif() {
        assert_parse_eq(compound_stmt(make_strspan("if foo:\n del bar\nelif foo:\n del baz"), 0), Ok((make_strspan(""),
            CompoundStatement::If(
                vec![
                    (
                        Expression::Name("foo".to_string()),
                        vec![
                            Statement::Del(vec![Expression::Name("bar".to_string())])
                        ]
                    ),
                    (
                        Expression::Name("foo".to_string()),
                        vec![
                            Statement::Del(vec![Expression::Name("baz".to_string())])
                        ]
                    ),
                ],
                None
            )
        )));
    }

    #[test]
    fn test_if_else() {
        assert_parse_eq(compound_stmt(make_strspan("if foo:\n del bar\nelse:\n del qux"), 0), Ok((make_strspan(""),
            CompoundStatement::If(
                vec![
                    (
                        Expression::Name("foo".to_string()),
                        vec![
                            Statement::Del(vec![Expression::Name("bar".to_string())])
                        ]
                    ),
                ],
                Some(
                    vec![
                        Statement::Del(vec![Expression::Name("qux".to_string())])
                    ]
                )
            )
        )));
    }

    #[test]
    fn test_elif_else() {
        assert_parse_eq(compound_stmt(make_strspan("if foo:\n del bar\nelif foo:\n del baz\nelse:\n del qux"), 0), Ok((make_strspan(""),
            CompoundStatement::If(
                vec![
                    (
                        Expression::Name("foo".to_string()),
                        vec![
                            Statement::Del(vec![Expression::Name("bar".to_string())])
                        ]
                    ),
                    (
                        Expression::Name("foo".to_string()),
                        vec![
                            Statement::Del(vec![Expression::Name("baz".to_string())])
                        ]
                    ),
                ],
                Some(
                    vec![
                        Statement::Del(vec![Expression::Name("qux".to_string())])
                    ]
                )
            )
        )));
    }

    #[test]
    fn test_nested_if() {
        assert_parse_eq(compound_stmt(make_strspan("if foo:\n if foo:\n  del bar"), 0), Ok((make_strspan(""),
            CompoundStatement::If(
                vec![
                    (
                        Expression::Name("foo".to_string()),
                        vec![
                            Statement::Compound(Box::new(
                              CompoundStatement::If(
                                  vec![
                                      (
                                          Expression::Name("foo".to_string()),
                                          vec![
                                              Statement::Del(vec![Expression::Name("bar".to_string())])
                                          ]
                                      ),
                                  ],
                                  None
                                )
                            ))
                        ]
                    ),
                ],
                None
            )
        )));
    }

    #[test]
    fn test_dangling_else_1() {
        assert_parse_eq(compound_stmt(make_strspan("if foo:\n if foo:\n  del bar\nelse:\n del qux"), 0), Ok((make_strspan(""),
            CompoundStatement::If(
                vec![
                    (
                        Expression::Name("foo".to_string()),
                        vec![
                            Statement::Compound(Box::new(
                              CompoundStatement::If(
                                  vec![
                                      (
                                          Expression::Name("foo".to_string()),
                                          vec![
                                              Statement::Del(vec![Expression::Name("bar".to_string())])
                                          ]
                                      ),
                                  ],
                                  None
                                )
                            ))
                        ]
                    ),
                ],
                Some(
                    vec![
                        Statement::Del(vec![Expression::Name("qux".to_string())])
                    ]
                )
            )
        )));
    }

    #[test]
    fn test_dangling_else_2() {
        assert_parse_eq(compound_stmt(make_strspan("if foo:\n if foo:\n  del bar\n else:\n  del qux"), 0), Ok((make_strspan(""),
            CompoundStatement::If(
                vec![
                    (
                        Expression::Name("foo".to_string()),
                        vec![
                            Statement::Compound(Box::new(
                              CompoundStatement::If(
                                  vec![
                                      (
                                          Expression::Name("foo".to_string()),
                                          vec![
                                              Statement::Del(vec![Expression::Name("bar".to_string())])
                                          ]
                                      ),
                                  ],
                                  Some(
                                      vec![
                                          Statement::Del(vec![Expression::Name("qux".to_string())])
                                      ]
                                  )
                                )
                            ))
                        ]
                    ),
                ],
                None
            )
        )));
    }

    #[test]
    fn test_while() {
        assert_parse_eq(compound_stmt(make_strspan("while foo:\n del bar"), 0), Ok((make_strspan(""),
            CompoundStatement::While(
                Expression::Name("foo".to_string()),
                vec![
                    Statement::Del(vec![Expression::Name("bar".to_string())])
                ],
                None
            )
        )));
    }

    #[test]
    fn test_while_else() {
        assert_parse_eq(compound_stmt(make_strspan("while foo:\n del bar\nelse:\n del qux"), 0), Ok((make_strspan(""),
            CompoundStatement::While(
                Expression::Name("foo".to_string()),
                vec![
                    Statement::Del(vec![Expression::Name("bar".to_string())])
                ],
                Some(
                    vec![
                        Statement::Del(vec![Expression::Name("qux".to_string())])
                    ]
                )
            )
        )));
    }

    #[test]
    fn test_for() {
        assert_parse_eq(compound_stmt(make_strspan("for foo in bar:\n del baz"), 0), Ok((make_strspan(""),
            CompoundStatement::For {
                async: false,
                item: vec![Expression::Name("foo".to_string())],
                iterator: vec![Expression::Name("bar".to_string())],
                for_block: vec![
                    Statement::Del(vec![Expression::Name("baz".to_string())])
                ],
                else_block: None
            }
        )));
    }

    #[test]
    fn test_for_else() {
        assert_parse_eq(compound_stmt(make_strspan("for foo in bar:\n del baz\nelse:\n del qux"), 0), Ok((make_strspan(""),
            CompoundStatement::For {
                async: false,
                item: vec![Expression::Name("foo".to_string())],
                iterator: vec![Expression::Name("bar".to_string())],
                for_block: vec![
                    Statement::Del(vec![Expression::Name("baz".to_string())])
                ],
                else_block: Some(
                    vec![
                        Statement::Del(vec![Expression::Name("qux".to_string())])
                    ]
                )
            }
        )));
    }

    #[test]
    fn test_raise() {
        assert_parse_eq(small_stmt(make_strspan("raise")), Ok((make_strspan(""),
            Statement::Raise
        )));

        assert_parse_eq(small_stmt(make_strspan("raise exc")), Ok((make_strspan(""),
            Statement::RaiseExc(
                Expression::Name("exc".to_string()),
            )
        )));

        assert_parse_eq(small_stmt(make_strspan("raise exc from exc2")), Ok((make_strspan(""),
            Statement::RaiseExcFrom(
                Expression::Name("exc".to_string()),
                Expression::Name("exc2".to_string()),
            )
        )));
    }

    #[test]
    fn test_assign() {
        assert_parse_eq(small_stmt(make_strspan("foo = bar")), Ok((make_strspan(""),
            Statement::Assignment(
                vec![
                    Expression::Name("foo".to_string()),
                ],
                vec![
                    vec![
                        Expression::Name("bar".to_string()),
                    ],
                ],
            )
        )));

        assert_parse_eq(small_stmt(make_strspan("foo = bar = baz")), Ok((make_strspan(""),
            Statement::Assignment(
                vec![
                    Expression::Name("foo".to_string()),
                ],
                vec![
                    vec![
                        Expression::Name("bar".to_string()),
                    ],
                    vec![
                        Expression::Name("baz".to_string()),
                    ],
                ],
            )
        )));
    }

    #[test]
    fn test_augassign() {
        assert_parse_eq(small_stmt(make_strspan("foo:bar = baz")), Ok((make_strspan(""),
            Statement::TypedAssignment(
                vec![
                    Expression::Name("foo".to_string()),
                ],
                Expression::Name("bar".to_string()),
                vec![
                    Expression::Name("baz".to_string()),
                ],
            )
        )));
    }

    #[test]
    fn test_unpack_assign() {
        assert_parse_eq(small_stmt(make_strspan("foo, bar = baz, qux")), Ok((make_strspan(""),
            Statement::Assignment(
                vec![
                    Expression::Name("foo".to_string()),
                    Expression::Name("bar".to_string()),
                ],
                vec![
                    vec![
                        Expression::Name("baz".to_string()),
                        Expression::Name("qux".to_string()),
                    ],
                ],
            )
        )));

        assert_parse_eq(small_stmt(make_strspan("foo = bar = baz")), Ok((make_strspan(""),
            Statement::Assignment(
                vec![
                    Expression::Name("foo".to_string()),
                ],
                vec![
                    vec![
                        Expression::Name("bar".to_string()),
                    ],
                    vec![
                        Expression::Name("baz".to_string()),
                    ],
                ],
            )
        )));
    }

    #[test]
    fn test_with() {
        assert_parse_eq(with_stmt(make_strspan("with foo:\n del bar"), 0), Ok((make_strspan(""),
            CompoundStatement::With(
                vec![
                    (Expression::Name("foo".to_string()), None),
                ],
                vec![
                    Statement::Del(vec![Expression::Name("bar".to_string())])
                ],
            )
        )));

        assert_parse_eq(with_stmt(make_strspan("with foo as bar:\n del baz"), 0), Ok((make_strspan(""),
            CompoundStatement::With(
                vec![
                    (Expression::Name("foo".to_string()), Some(Expression::Name("bar".to_string()))),
                ],
                vec![
                    Statement::Del(vec![Expression::Name("baz".to_string())])
                ],
            )
        )));
    }

    #[test]
    fn test_try() {
        assert_parse_eq(try_stmt(make_strspan("try:\n del foo\nexcept Bar:\n del baz"), 0), Ok((make_strspan(""),
            CompoundStatement::Try(Try {
                try_block: vec![
                    Statement::Del(vec![Expression::Name("foo".to_string())]),
                ],
                except_clauses: vec![
                    (
                        Expression::Name("Bar".to_string()),
                        None,
                        vec![Statement::Del(vec![Expression::Name("baz".to_string())])],
                    ),
                ],
                last_except: vec![],
                else_block: vec![],
                finally_block: vec![],
            })
        )));

        assert_parse_eq(try_stmt(make_strspan("try:\n del foo\nexcept:\n del baz"), 0), Ok((make_strspan(""),
            CompoundStatement::Try(Try {
                try_block: vec![
                    Statement::Del(vec![Expression::Name("foo".to_string())]),
                ],
                except_clauses: vec![],
                last_except: vec![
                    Statement::Del(vec![Expression::Name("baz".to_string())]),
                ],
                else_block: vec![],
                finally_block: vec![],
            })
        )));

        assert_parse_eq(try_stmt(make_strspan("try:\n del foo\nelse:\n del baz"), 0), Ok((make_strspan(""),
            CompoundStatement::Try(Try {
                try_block: vec![
                    Statement::Del(vec![Expression::Name("foo".to_string())]),
                ],
                except_clauses: vec![],
                last_except: vec![],
                else_block: vec![
                    Statement::Del(vec![Expression::Name("baz".to_string())]),
                ],
                finally_block: vec![],
            })
        )));

        assert_parse_eq(try_stmt(make_strspan("try:\n del foo\nfinally:\n del baz"), 0), Ok((make_strspan(""),
            CompoundStatement::Try(Try {
                try_block: vec![
                    Statement::Del(vec![Expression::Name("foo".to_string())]),
                ],
                except_clauses: vec![],
                last_except: vec![],
                else_block: vec![],
                finally_block: vec![
                    Statement::Del(vec![Expression::Name("baz".to_string())]),
                ],
            })
        )));
    }

    #[test]
    fn test_import() {
        assert_parse_eq(statement(make_strspan("import foo"), 0), Ok((make_strspan(""),
            vec![Statement::Import(Import::Import {
                names: vec![(vec!["foo".to_string()], None)],
            })]
        )));
    }
}
