use nom::types::CompleteStr;

use helpers::*;
use expressions::{Expression, possibly_empty_testlist, test, yield_expr};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Import {
    /// `from x import y`
    ImportFrom {
        /// For `from .....x import y`, this is 5
        leading_dots: usize,
        /// For `from .....x import y`, this `x`
        path: Vec<Name>,
        /// For `from x import y, z`, this `vec![(y, None), (vec![z], None)]`.
        /// For `from x import y as z`, this `vec![(y, Some(z))]`.
        /// For `from x import *`, this is `vec![]`.
        names: Vec<(Name, Option<Name>)>
    },
    /// `import x.y as z, foo.bar` is
    /// `Import::Import(vec![(vec![x, y], Some(z)), (vec![foo, bar], None)])`.
    Import { names: Vec<(Vec<Name>, Option<Name>)> },
}

#[derive(Clone, Debug, PartialEq)]
pub enum Statement {
    Pass,
    Del(Vec<Name>),
    Break,
    Continue,
    Return(Vec<Expression>),
    RaiseExcFrom(Expression, Expression),
    RaiseExc(Expression),
    Raise,
    Global(Vec<Name>),
    Nonlocal(Vec<Name>),
    Assert(Expression, Option<Expression>),
    Import(Import),
    Expression(Expression),
    // TODO

    Compound(Box<CompoundStatement>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum CompoundStatement {
    // TODO
    If(Vec<(Test, Vec<Statement>)>, Option<Vec<Statement>>),
    For(Vec<Expr>, Vec<Expr>, Vec<Statement>, Option<Vec<Statement>>),
    While(Test, Vec<Statement>, Option<Vec<Statement>>),
}


/*********************************************************************
 * Base statement parsers
 *********************************************************************/

// stmt: simple_stmt | compound_stmt
named_args!(pub statement(first_indent: usize, indent: usize) <CompleteStr, Vec<Statement>>,
  alt!(
    call!(simple_stmt, first_indent)
  | call!(compound_stmt, first_indent, indent) => { |stmt| vec![Statement::Compound(Box::new(stmt))] }
  )
);

// simple_stmt: small_stmt (';' small_stmt)* [';'] NEWLINE
named_args!(simple_stmt(indent: usize) <CompleteStr, Vec<Statement>>,
  do_parse!(
    count!(char!(' '), indent) >>
    stmts: separated_nonempty_list!(semicolon, call!(small_stmt)) >>
    opt!(semicolon) >> (
      stmts
    )
  )
);

// small_stmt: (expr_stmt | del_stmt | pass_stmt | flow_stmt |
//             import_stmt | global_stmt | nonlocal_stmt | assert_stmt)
named!(small_stmt<CompleteStr, Statement>,
  alt!(
    del_stmt => { |atoms| Statement::Del(atoms) }
  | pass_stmt
  | flow_stmt
  | import_stmt
  | global_stmt
  | nonlocal_stmt
  | assert_stmt
    // TODO
  )
);

/*********************************************************************
 * Expression statements
 *********************************************************************/

// expr_stmt: testlist_star_expr (annassign | augassign (yield_expr|testlist) |
//                     ('=' (yield_expr|testlist_star_expr))*)
// TODO

// annassign: ':' test ['=' test]
// TODO

// testlist_star_expr: (test|star_expr) (',' (test|star_expr))* [',']
// TODO

// augassign: ('+=' | '-=' | '*=' | '@=' | '/=' | '%=' | '&=' | '|=' | '^=' |
//            '<<=' | '>>=' | '**=' | '//=')
// TODO

/*********************************************************************
 * Small statements
 *********************************************************************/

// del_stmt: 'del' exprlist
named!(del_stmt<CompleteStr, Vec<String>>,
  preceded!(tuple!(tag!("del"), space_sep2), ws2!(many1!(name)))
);

// pass_stmt: 'pass'
named!(pass_stmt<CompleteStr, Statement>,
  map!(tag!("pass"), |_| Statement::Pass)
);

// flow_stmt: break_stmt | continue_stmt | return_stmt | raise_stmt | yield_stmt
// break_stmt: 'break'
// continue_stmt: 'continue'
// return_stmt: 'return' [testlist]
// yield_stmt: yield_expr
named!(flow_stmt<CompleteStr, Statement>,
  alt!(
    tag!("break") => { |_| Statement::Break }
  | tag!("continue") => { |_| Statement::Continue }
  | preceded!(tuple!(tag!("return"), space_sep2), ws2!(possibly_empty_testlist)) => { |e| Statement::Return(e) }
  | yield_expr => { |e: Box<_>| Statement::Expression(*e) }
  | raise_stmt
  )
);

// raise_stmt: 'raise' [test ['from' test]]
named!(raise_stmt<CompleteStr, Statement>,
  do_parse!(
    tag!("raise") >>
    t: opt!(tuple!(
      preceded!(space_sep2, test),
      opt!(preceded!(tuple!(space_sep2, tag!("from"), space_sep2), test))
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
named!(global_stmt<CompleteStr, Statement>,
  map!(preceded!(tuple!(tag!("global"), space_sep2),
    ws2!(separated_nonempty_list!(char!(','), name))
  ), |names| Statement::Global(names))
);

// nonlocal_stmt: 'nonlocal' NAME (',' NAME)*
named!(nonlocal_stmt<CompleteStr, Statement>,
  map!(preceded!(tuple!(tag!("nonlocal"), space_sep2),
    ws2!(separated_nonempty_list!(char!(','), name))
  ), |names| Statement::Nonlocal(names))
);

// assert_stmt: 'assert' test [',' test]
named!(assert_stmt<CompleteStr, Statement>,
  do_parse!(
    tag!("assert") >>
    space_sep2 >>
    assertion: test >>
    msg: opt!(preceded!(ws2!(char!(',')), test)) >> (
      Statement::Assert(*assertion, msg.map(|m| *m))
    )
  )
);

/*********************************************************************
 * Imports
 *********************************************************************/

// import_stmt: import_name | import_from
named!(import_stmt<CompleteStr, Statement>,
  alt!(
    import_name => { |i| Statement::Import(i) }
  | import_from => { |i| Statement::Import(i) }
  )
);

// import_name: 'import' dotted_as_names
named!(import_name<CompleteStr, Import>,
  map!(preceded!(tuple!(tag!("import"), space_sep2), dotted_as_names),
    |names| Import::Import { names }
  )
);

// import_from: ('from' (('.' | '...')* dotted_name | ('.' | '...')+)
//               'import' ('*' | '(' import_as_names ')' | import_as_names))
//
// the explicit presence of '...' is for parsers that use a lexer, because
// they would recognize ... as an ellipsis.
named!(import_from<CompleteStr, Import>,
  do_parse!(
    tag!("from") >>
    space_sep2 >>
    import_from: alt!(
      preceded!(char!('.'), do_parse!(
        leading_dots: ws2!(map!(many0!(char!('.')), |dots| dots.len()+1)) >>
        from_name: opt!(dotted_name) >> (
          (leading_dots, from_name.unwrap_or(Vec::new()))
        )
      ))
    | dotted_name => { |n| (0, n) }
    ) >>
    space_sep2 >>
    tag!("import") >>
    space_sep2 >>
    names: alt!(
      char!('*') => { |_| Vec::new() }
    | ws2!(delimited!(char!('('), import_as_names, char!(')')))
    | import_as_names
    ) >> ({
      let (leading_dots, path) = import_from;
      Import::ImportFrom { leading_dots, path, names }
    })
  )
);


// import_as_name: NAME ['as' NAME]
named!(import_as_name<CompleteStr, (Name, Option<Name>)>,
  tuple!(name, opt!(do_parse!(
    space_sep2 >>
    tag!("as") >>
    space_sep2 >>
    name: name >> (
      name
    )
  )))
);

// dotted_as_name: dotted_name ['as' NAME]
named!(dotted_as_name<CompleteStr, (Vec<Name>, Option<Name>)>,
  tuple!(dotted_name, opt!(do_parse!(
    space_sep2 >>
    tag!("as") >>
    space_sep2 >>
    name: name >> (
      name
    )
  )))
);

// import_as_names: import_as_name (',' import_as_name)* [',']
named!(import_as_names<CompleteStr, Vec<(Name, Option<Name>)>>,
  ws2!(terminated!(separated_nonempty_list!(char!(','), import_as_name), opt!(char!(','))))
);

// dotted_as_names: dotted_as_name (',' dotted_as_name)*
named!(dotted_as_names<CompleteStr, Vec<(Vec<Name>, Option<Name>)>>,
  separated_nonempty_list!(ws2!(char!(',')), dotted_as_name)
);

// dotted_name: NAME ('.' NAME)*
named!(dotted_name<CompleteStr, Vec<Name>>,
  separated_nonempty_list!(ws2!(char!('.')), name)
);

/*********************************************************************
 * Blocks
 *********************************************************************/

// suite: simple_stmt | NEWLINE INDENT stmt+ DEDENT
named_args!(block(indent: usize) <CompleteStr, Vec<Statement>>,
  alt!(
    do_parse!(
      newline >>
      new_indent: do_parse!(
        count!(char!(' '), indent) >>
        new_spaces: many1!(char!(' ')) >> ({
          indent + new_spaces.len()
        })
      ) >>
      stmts: fold_many1!(
        call!(statement, 0, new_indent),
        Vec::new(),
        |mut acc: Vec<_>, stmt| { acc.extend(stmt); acc }
      ) >> (
        stmts
      )
    )
  | call!(simple_stmt, 0)
  )
);
named_args!(cond_and_block(indent: usize) <CompleteStr, (String, Vec<Statement>)>,
  do_parse!(
    cond: ws2!(tag!("foo")) >>
    ws2!(char!(':')) >>
    block: call!(block, indent) >> (
      (cond.to_string(), block)
    )
  )
);


// compound_stmt: if_stmt | while_stmt | for_stmt | try_stmt | with_stmt | funcdef | classdef | decorated | async_stmt
named_args!(compound_stmt(first_indent: usize, indent: usize) <CompleteStr, CompoundStatement>,
  preceded!(
    count!(char!(' '), first_indent),
    alt!(
      call!(if_stmt, indent)
    | call!(for_stmt, indent)
    | call!(while_stmt, indent)
    // TODO
    )
  )
);

// async_stmt: ASYNC (funcdef | with_stmt | for_stmt)
// TODO

named_args!(else_block(indent: usize) <CompleteStr, Option<Vec<Statement>>>,
  opt!(
    preceded!(
      tuple!(newline, count!(char!(' '), indent), tag!("else"), ws2!(char!(':'))),
      call!(block, indent)
    )
  )
);

// if_stmt: 'if' test ':' suite ('elif' test ':' suite)* ['else' ':' suite]
named_args!(if_stmt(indent: usize) <CompleteStr, CompoundStatement>,
  do_parse!(
    tag!("if ") >>
    if_block: call!(cond_and_block, indent) >>
    elif_blocks: many0!(
      preceded!(
        tuple!(newline, count!(char!(' '), indent), tag!("elif ")),
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
named_args!(while_stmt(indent: usize) <CompleteStr, CompoundStatement>,
  do_parse!(
    tag!("while ") >>
    while_block: call!(cond_and_block, indent) >>
    else_block: call!(else_block, indent) >> ({
      let (cond, while_block) = while_block;
      CompoundStatement::While(cond, while_block, else_block)
    })
  )
);

// for_stmt: 'for' exprlist 'in' testlist ':' suite ['else' ':' suite]
named_args!(for_stmt(indent: usize) <CompleteStr, CompoundStatement>,
  do_parse!(
    tag!("for ") >>
    item: tag!("foo") >>
    tag!(" in ") >>
    iterator: tag!("bar") >>
    ws2!(char!(':')) >>
    for_block: call!(block, indent) >>
    else_block: call!(else_block, indent) >> ({
      CompoundStatement::For(vec![item.to_string()], vec![iterator.to_string()], for_block, else_block)
    })
  )
);

// try_stmt: ('try' ':' suite
//            ((except_clause ':' suite)+
//             ['else' ':' suite]
//             ['finally' ':' suite] |
//             'finally' ':' suite))
// TODO

// with_stmt: 'with' with_item (',' with_item)*  ':' suite
// TODO

// with_item: test ['as' expr]
// TODO

// except_clause: 'except' [test ['as' NAME]]
// TODO

// classdef: 'class' NAME ['(' [arglist] ')'] ':' suite
// TODO

/*********************************************************************
 * Unit tests
 *********************************************************************/

#[cfg(test)]
mod tests {
    use super::*;
    use nom::types::CompleteStr as CS;

    #[test]
    fn test_statement_indent() {
        assert_eq!(statement(CS("del foo"), 0, 0), Ok((CS(""), vec![Statement::Del(vec!["foo".to_string()])])));
        assert_eq!(statement(CS(" del foo"), 1, 1), Ok((CS(""), vec![Statement::Del(vec!["foo".to_string()])])));
        assert!(statement(CS("del foo"), 1, 1).is_err());
        assert!(statement(CS(" del foo"), 0, 0).is_err());
    }

    #[test]
    fn test_block() {
        assert_eq!(block(CS("\n del foo"), 0), Ok((CS(""), vec![Statement::Del(vec!["foo".to_string()])])));
        assert_eq!(block(CS("\n  del foo"), 1), Ok((CS(""), vec![Statement::Del(vec!["foo".to_string()])])));
        assert_eq!(block(CS("\n      del foo"), 1), Ok((CS(""), vec![Statement::Del(vec!["foo".to_string()])])));
        assert!(block(CS("\ndel foo"), 0).is_err());
        assert!(block(CS("\ndel foo"), 1).is_err());
        assert!(block(CS("\n del foo"), 1).is_err());
    }

    #[test]
    fn test_if() {
        assert_eq!(compound_stmt(CS("if foo:\n del bar"), 0, 0), Ok((CS(""),
            CompoundStatement::If(
                vec![
                    (
                        "foo".to_string(),
                        vec![
                            Statement::Del(vec!["bar".to_string()])
                        ]
                    ),
                ],
                None
            )
        )));
    }

    #[test]
    fn test_elif() {
        assert_eq!(compound_stmt(CS("if foo:\n del bar\nelif foo:\n del baz"), 0, 0), Ok((CS(""),
            CompoundStatement::If(
                vec![
                    (
                        "foo".to_string(),
                        vec![
                            Statement::Del(vec!["bar".to_string()])
                        ]
                    ),
                    (
                        "foo".to_string(),
                        vec![
                            Statement::Del(vec!["baz".to_string()])
                        ]
                    ),
                ],
                None
            )
        )));
    }

    #[test]
    fn test_if_else() {
        assert_eq!(compound_stmt(CS("if foo:\n del bar\nelse:\n del qux"), 0, 0), Ok((CS(""),
            CompoundStatement::If(
                vec![
                    (
                        "foo".to_string(),
                        vec![
                            Statement::Del(vec!["bar".to_string()])
                        ]
                    ),
                ],
                Some(
                    vec![
                        Statement::Del(vec!["qux".to_string()])
                    ]
                )
            )
        )));
    }

    #[test]
    fn test_elif_else() {
        assert_eq!(compound_stmt(CS("if foo:\n del bar\nelif foo:\n del baz\nelse:\n del qux"), 0, 0), Ok((CS(""),
            CompoundStatement::If(
                vec![
                    (
                        "foo".to_string(),
                        vec![
                            Statement::Del(vec!["bar".to_string()])
                        ]
                    ),
                    (
                        "foo".to_string(),
                        vec![
                            Statement::Del(vec!["baz".to_string()])
                        ]
                    ),
                ],
                Some(
                    vec![
                        Statement::Del(vec!["qux".to_string()])
                    ]
                )
            )
        )));
    }

    #[test]
    fn test_nested_if() {
        assert_eq!(compound_stmt(CS("if foo:\n if foo:\n  del bar"), 0, 0), Ok((CS(""),
            CompoundStatement::If(
                vec![
                    (
                        "foo".to_string(),
                        vec![
                            Statement::Compound(Box::new(
                              CompoundStatement::If(
                                  vec![
                                      (
                                          "foo".to_string(),
                                          vec![
                                              Statement::Del(vec!["bar".to_string()])
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
        assert_eq!(compound_stmt(CS("if foo:\n if foo:\n  del bar\nelse:\n del qux"), 0, 0), Ok((CS(""),
            CompoundStatement::If(
                vec![
                    (
                        "foo".to_string(),
                        vec![
                            Statement::Compound(Box::new(
                              CompoundStatement::If(
                                  vec![
                                      (
                                          "foo".to_string(),
                                          vec![
                                              Statement::Del(vec!["bar".to_string()])
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
                        Statement::Del(vec!["qux".to_string()])
                    ]
                )
            )
        )));
    }

    #[test]
    fn test_dangling_else_2() {
        assert_eq!(compound_stmt(CS("if foo:\n if foo:\n  del bar\n else:\n  del qux"), 0, 0), Ok((CS(""),
            CompoundStatement::If(
                vec![
                    (
                        "foo".to_string(),
                        vec![
                            Statement::Compound(Box::new(
                              CompoundStatement::If(
                                  vec![
                                      (
                                          "foo".to_string(),
                                          vec![
                                              Statement::Del(vec!["bar".to_string()])
                                          ]
                                      ),
                                  ],
                                  Some(
                                      vec![
                                          Statement::Del(vec!["qux".to_string()])
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
        assert_eq!(compound_stmt(CS("while foo:\n del bar"), 0, 0), Ok((CS(""),
            CompoundStatement::While(
                "foo".to_string(),
                vec![
                    Statement::Del(vec!["bar".to_string()])
                ],
                None
            )
        )));
    }

    #[test]
    fn test_while_else() {
        assert_eq!(compound_stmt(CS("while foo:\n del bar\nelse:\n del qux"), 0, 0), Ok((CS(""),
            CompoundStatement::While(
                "foo".to_string(),
                vec![
                    Statement::Del(vec!["bar".to_string()])
                ],
                Some(
                    vec![
                        Statement::Del(vec!["qux".to_string()])
                    ]
                )
            )
        )));
    }

    #[test]
    fn test_for() {
        assert_eq!(compound_stmt(CS("for foo in bar:\n del baz"), 0, 0), Ok((CS(""),
            CompoundStatement::For(
                vec!["foo".to_string()],
                vec!["bar".to_string()],
                vec![
                    Statement::Del(vec!["baz".to_string()])
                ],
                None
            )
        )));
    }

    #[test]
    fn test_for_else() {
        assert_eq!(compound_stmt(CS("for foo in bar:\n del baz\nelse:\n del qux"), 0, 0), Ok((CS(""),
            CompoundStatement::For(
                vec!["foo".to_string()],
                vec!["bar".to_string()],
                vec![
                    Statement::Del(vec!["baz".to_string()])
                ],
                Some(
                    vec![
                        Statement::Del(vec!["qux".to_string()])
                    ]
                )
            )
        )));
    }

    #[test]
    fn test_raise() {
        use expressions::Atom;
        assert_eq!(small_stmt(CS("raise")), Ok((CS(""),
            Statement::Raise
        )));

        assert_eq!(small_stmt(CS("raise exc")), Ok((CS(""),
            Statement::RaiseExc(
                Expression::Atom(Atom::Name("exc".to_string())),
            )
        )));

        assert_eq!(small_stmt(CS("raise exc from exc2")), Ok((CS(""),
            Statement::RaiseExcFrom(
                Expression::Atom(Atom::Name("exc".to_string())),
                Expression::Atom(Atom::Name("exc2".to_string())),
            )
        )));
    }
}
