use nom::types::CompleteStr;

use helpers::*;
use expressions::{Expression, possibly_empty_testlist, test};

#[derive(Clone, Debug, PartialEq)]
pub enum SmallStatement {
    // TODO
    Del(Vec<Name>),
    Break,
    Continue,
    Return(Vec<Expression>),
    RaiseExcFrom(Expression, Expression),
    RaiseExc(Expression),
    Raise,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Statement {
    Simple(Vec<SmallStatement>),
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
named_args!(pub statement(first_indent: usize, indent: usize) <CompleteStr, Statement>,
  alt!(
    call!(simple_stmt, first_indent) => { |stmts| Statement::Simple(stmts) }
  | call!(compound_stmt, first_indent, indent) => { |stmt| Statement::Compound(Box::new(stmt)) }
  )
);

// simple_stmt: small_stmt (';' small_stmt)* [';'] NEWLINE
// TODO: Use separated_nonempty_list
named_args!(simple_stmt(indent: usize) <CompleteStr, Vec<SmallStatement>>,
  do_parse!(
    count!(char!(' '), indent) >>
    first_stmts: many0!(terminated!(call!(small_stmt), semicolon)) >>
    last_stmt: small_stmt >>
    opt!(semicolon) >> ({
      let mut stmts = first_stmts;
      stmts.push(last_stmt);
      stmts
    })
  )
);

// small_stmt: (expr_stmt | del_stmt | pass_stmt | flow_stmt |
//             import_stmt | global_stmt | nonlocal_stmt | assert_stmt)
named!(small_stmt<CompleteStr, SmallStatement>,
  alt!(
    del_stmt => { |atoms| SmallStatement::Del(atoms) }
  | flow_stmt
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
  preceded!(tag!("del "), ws2!(many1!(name))) // TODO
);

// pass_stmt: 'pass'
named!(pass_stmt<CompleteStr, ()>,
  map!(tag!("pass"), |_| ())
);

// flow_stmt: break_stmt | continue_stmt | return_stmt | raise_stmt | yield_stmt
// break_stmt: 'break'
// continue_stmt: 'continue'
// return_stmt: 'return' [testlist]
// yield_stmt: yield_expr
named!(flow_stmt<CompleteStr, SmallStatement>,
  alt!(
    tag!("break") => { |_| SmallStatement::Break }
  | tag!("continue") => { |_| SmallStatement::Continue }
  | preceded!(tag!("return "), ws2!(possibly_empty_testlist)) => { |e| SmallStatement::Return(e) }
  //| yield_expr // TODO
  | raise_stmt
  )
);

// raise_stmt: 'raise' [test ['from' test]]
named!(raise_stmt<CompleteStr, SmallStatement>,
  do_parse!(
    tag!("raise") >>
    t: opt!(tuple!(
      preceded!(char!(' '), test),
      opt!(ws2!(preceded!(tag!("from"), test)))
    )) >> (
      match t {
        Some((exc, Some(from_exc))) => SmallStatement::RaiseExcFrom(*exc, *from_exc),
        Some((exc, None)) => SmallStatement::RaiseExc(*exc),
        None => SmallStatement::Raise,
      }
    )
  )
);

// global_stmt: 'global' NAME (',' NAME)*
// TODO

// nonlocal_stmt: 'nonlocal' NAME (',' NAME)*
// TODO

// assert_stmt: 'assert' test [',' test]
// TODO

/*********************************************************************
 * Imports
 *********************************************************************/

// import_stmt: import_name | import_from
// TODO

// import_name: 'import' dotted_as_names
// TODO

// import_from: ('from' (('.' | '...')* dotted_name | ('.' | '...')+)
//               'import' ('*' | '(' import_as_names ')' | import_as_names))
// TODO

// import_as_name: NAME ['as' NAME]
// TODO

// dotted_as_name: dotted_name ['as' NAME]
// TODO

// import_as_names: import_as_name (',' import_as_name)* [',']
// TODO

// dotted_as_names: dotted_as_name (',' dotted_as_name)*
// TODO

// dotted_name: NAME ('.' NAME)*

/*********************************************************************
 * Blocks
 *********************************************************************/

// suite: simple_stmt | NEWLINE INDENT stmt+ DEDENT
named_args!(block(indent: usize) <CompleteStr, Vec<Statement>>,
  // TODO: simple_stmt
  do_parse!(
    newline >>
    new_indent: do_parse!(
      count!(char!(' '), indent) >>
      new_spaces: many1!(char!(' ')) >> ({
        indent + new_spaces.len()
      })
    ) >>
    stmt: many1!(call!(statement, 0, new_indent)) >> (
      stmt
    )
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

/*********************************************************************
 * Unit tests
 *********************************************************************/

#[cfg(test)]
mod tests {
    use super::*;
    use nom::types::CompleteStr as CS;

    #[test]
    fn test_statement_indent() {
        assert_eq!(statement(CS("del foo"), 0, 0), Ok((CS(""), Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])]))));
        assert_eq!(statement(CS(" del foo"), 1, 1), Ok((CS(""), Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])]))));
        assert!(statement(CS("del foo"), 1, 1).is_err());
        assert!(statement(CS(" del foo"), 0, 0).is_err());
    }

    #[test]
    fn test_block() {
        assert_eq!(block(CS("\n del foo"), 0), Ok((CS(""), vec![Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])])])));
        assert_eq!(block(CS("\n  del foo"), 1), Ok((CS(""), vec![Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])])])));
        assert_eq!(block(CS("\n      del foo"), 1), Ok((CS(""), vec![Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])])])));
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
                            Statement::Simple(vec![
                                SmallStatement::Del(vec!["bar".to_string()])
                            ])
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
                            Statement::Simple(vec![
                                SmallStatement::Del(vec!["bar".to_string()])
                            ])
                        ]
                    ),
                    (
                        "foo".to_string(),
                        vec![
                            Statement::Simple(vec![
                                SmallStatement::Del(vec!["baz".to_string()])
                            ])
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
                            Statement::Simple(vec![
                                SmallStatement::Del(vec!["bar".to_string()])
                            ])
                        ]
                    ),
                ],
                Some(
                    vec![
                        Statement::Simple(vec![
                            SmallStatement::Del(vec!["qux".to_string()])
                        ])
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
                            Statement::Simple(vec![
                                SmallStatement::Del(vec!["bar".to_string()])
                            ])
                        ]
                    ),
                    (
                        "foo".to_string(),
                        vec![
                            Statement::Simple(vec![
                                SmallStatement::Del(vec!["baz".to_string()])
                            ])
                        ]
                    ),
                ],
                Some(
                    vec![
                        Statement::Simple(vec![
                            SmallStatement::Del(vec!["qux".to_string()])
                        ])
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
                                              Statement::Simple(vec![
                                                  SmallStatement::Del(vec!["bar".to_string()])
                                              ])
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
                                              Statement::Simple(vec![
                                                  SmallStatement::Del(vec!["bar".to_string()])
                                              ])
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
                        Statement::Simple(vec![
                            SmallStatement::Del(vec!["qux".to_string()])
                        ])
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
                                              Statement::Simple(vec![
                                                  SmallStatement::Del(vec!["bar".to_string()])
                                              ])
                                          ]
                                      ),
                                  ],
                                  Some(
                                      vec![
                                          Statement::Simple(vec![
                                              SmallStatement::Del(vec!["qux".to_string()])
                                          ])
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
                    Statement::Simple(vec![
                        SmallStatement::Del(vec!["bar".to_string()])
                    ])
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
                    Statement::Simple(vec![
                        SmallStatement::Del(vec!["bar".to_string()])
                    ])
                ],
                Some(
                    vec![
                        Statement::Simple(vec![
                            SmallStatement::Del(vec!["qux".to_string()])
                        ])
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
                    Statement::Simple(vec![
                        SmallStatement::Del(vec!["baz".to_string()])
                    ])
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
                    Statement::Simple(vec![
                        SmallStatement::Del(vec!["baz".to_string()])
                    ])
                ],
                Some(
                    vec![
                        Statement::Simple(vec![
                            SmallStatement::Del(vec!["qux".to_string()])
                        ])
                    ]
                )
            )
        )));
    }

    #[test]
    fn test_raise() {
        use expressions::Atom;
        assert_eq!(small_stmt(CS("raise")), Ok((CS(""),
            SmallStatement::Raise
        )));

        assert_eq!(small_stmt(CS("raise exc")), Ok((CS(""),
            SmallStatement::RaiseExc(
                Expression::Atom(Atom::Name("exc".to_string())),
            )
        )));

        assert_eq!(small_stmt(CS("raise exc from exc2")), Ok((CS(""),
            SmallStatement::RaiseExcFrom(
                Expression::Atom(Atom::Name("exc".to_string())),
                Expression::Atom(Atom::Name("exc2".to_string())),
            )
        )));
    }
}
