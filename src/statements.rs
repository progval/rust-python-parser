use helpers::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SmallStatement {
    // TODO
    Del(Vec<Name>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Statement {
    Simple(Vec<SmallStatement>),
    Compound(Box<CompoundStatement>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CompoundStatement {
    // TODO
    If(Vec<(Test, Vec<Statement>)>, Option<Vec<Statement>>),
}


named_args!(pub statement(first_indent: usize, indent: usize) <&str, Statement>,
  alt!(
    call!(simple_stmt, first_indent) => { |stmts| Statement::Simple(stmts) }
  | terminated!(call!(compound_stmt, first_indent, indent), newline) => { |stmt| Statement::Compound(Box::new(stmt)) }
  )
);

named_args!(simple_stmt(indent: usize) <&str, Vec<SmallStatement>>,
  do_parse!(
    count!(char!(' '), indent) >>
    first_stmts: many0!(terminated!(call!(small_stmt), semicolon)) >>
    last_stmt: small_stmt >>
    opt!(semicolon) >>
    newline >> ({
      let mut stmts = first_stmts;
      stmts.push(last_stmt);
      stmts
    })
  )
);

named_args!(block(indent: usize) <&str, Vec<Statement>>,
  do_parse!(
    new_indent: do_parse!(
      count!(char!(' '), indent) >>
      new_spaces: many1!(char!(' ')) >> (
        indent + new_spaces.len()
      )
    ) >>
    stmt: many1!(call!(statement, 0, new_indent)) >> (
      stmt
    )
  )
);

named_args!(cond_and_block(indent: usize) <&str, (String, Vec<Statement>)>,
  do_parse!(
    cond: ws2!(tag!("foo")) >>
    ws2!(char!(':')) >>
    newline >>
    block: call!(block, indent) >> (
      (cond.to_string(), block)
    )
  )
);

named_args!(compound_stmt(first_indent: usize, indent: usize) <&str, CompoundStatement>,
  do_parse!(
    count!(char!(' '), first_indent) >>
    content: alt!(
      tuple!(
        preceded!(tag!("if "), call!(cond_and_block, indent)),
        many0!(
          preceded!(
            tuple!(count!(char!(' '), indent), tag!("elif ")),
            call!(cond_and_block, indent)
          )
        ),
        opt!(
          preceded!(
            tuple!(count!(char!(' '), indent), tag!("else"), ws2!(char!(':')), newline),
            call!(block, indent)
          )
        )
      ) => { |(if_block, elif_blocks, else_block)| {
        let mut blocks: Vec<_> = elif_blocks;
        blocks.insert(0, if_block);
        CompoundStatement::If(blocks, else_block)
      }}
    ) >> (
      content
    )
  )
);

named!(small_stmt<&str, SmallStatement>,
  alt!(
    del_stmt => { |atoms| SmallStatement::Del(atoms) }
    // TODO
  )
);

named!(del_stmt<&str, Vec<String>>,
  preceded!(tag!("del "), ws2!(many1!(name)))
  // TODO
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_statement_indent() {
        assert_eq!(statement("del foo\n", 0, 0), Ok(("", Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])]))));
        assert_eq!(statement(" del foo\n", 1, 1), Ok(("", Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])]))));
        assert!(statement("del foo\n", 1, 1).is_err());
        assert!(statement(" del foo\n", 0, 0).is_err());
    }

    #[test]
    fn test_block() {
        assert_eq!(block(" del foo\n\n", 0), Ok(("\n", vec![Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])])])));
        assert_eq!(block("  del foo\n\n", 1), Ok(("\n", vec![Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])])])));
        assert_eq!(block("      del foo\n\n", 1), Ok(("\n", vec![Statement::Simple(vec![SmallStatement::Del(vec!["foo".to_string()])])])));
        assert!(block("del foo\n\n", 0).is_err());
        assert!(block("del foo\n\n", 1).is_err());
        assert!(block(" del foo\n\n", 1).is_err());
    }

    #[test]
    fn test_if() {
        assert_eq!(compound_stmt("if foo:\n del bar\n ", 0, 0), Ok((" ",
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
        assert_eq!(compound_stmt("if foo:\n del bar\nelif foo:\n del baz\n ", 0, 0), Ok((" ",
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
    fn test_else() {
        assert_eq!(compound_stmt("if foo:\n del bar\nelse:\n del qux\n ", 0, 0), Ok((" ",
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
        assert_eq!(compound_stmt("if foo:\n del bar\nelif foo:\n del baz\nelse:\n del qux\n ", 0, 0), Ok((" ",
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
        assert_eq!(compound_stmt("if foo:\n if foo:\n  del bar\n\n\n", 0, 0), Ok(("\n",
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
}
