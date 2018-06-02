use std::marker::PhantomData;

use nom::types::CompleteStr;

use helpers::*;
use expressions::{Expression, ExpressionParser, Arglist};
use functions::{decorated, Decorator, TypedArgsList};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AugAssignOp {
    Add,
    Sub,
    Mult,
    MatMult,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    Lshift,
    Rshift,
    Power,
    Floordiv,
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
    Expressions(Vec<Expression>),
    // `lhs = rhs1 = rhs2` -> `lhs, vec![rhs1, rhs2]`
    Assignment(Vec<Expression>, Vec<Vec<Expression>>),
    // `lhs: type = rhs` -> `lhs, type, rhs`
    TypedAssignment(Vec<Expression>, Expression, Vec<Expression>),
    // `lhs += rhs` -> `lhs, AugAssignOp::Add, rhs`
    AugmentedAssignment(Vec<Expression>, AugAssignOp, Vec<Expression>),

    Compound(Box<CompoundStatement>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Funcdef {
    pub async: bool,
    pub decorators: Vec<Decorator>,
    pub name: String,
    pub parameters: TypedArgsList,
    pub return_type: Option<Expression>,
    pub code: Vec<Statement>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Classdef {
    pub decorators: Vec<Decorator>,
    pub name: String,
    pub parameters: Arglist,
    pub code: Vec<Statement>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Try {
    pub try_block: Vec<Statement>,
    /// except `1 [as 2]: 3`
    pub except_clauses: Vec<(Expression, Option<Name>, Vec<Statement>)>,
    /// Empty iff no `except:` clause.
    pub last_except: Vec<Statement>,
    /// Empty iff no `else:` clause.
    pub else_block: Vec<Statement>,
    /// Empty iff no `finally:` clause.
    pub finally_block: Vec<Statement>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CompoundStatement {
    If(Vec<(Test, Vec<Statement>)>, Option<Vec<Statement>>),
    For { async: bool, item: Vec<Expression>, iterator: Vec<Expression>, for_block: Vec<Statement>, else_block: Option<Vec<Statement>> },
    While(Test, Vec<Statement>, Option<Vec<Statement>>),
    With(Vec<(Expression, Option<Expression>)>, Vec<Statement>),
    Funcdef(Funcdef),
    Classdef(Classdef),
    Try(Try),
}


macro_rules! call_test {
    ( $i:expr, $($args:tt)* ) => { call!($i, ExpressionParser::<NewlinesAreNotSpaces>::test, $($args)*) }
}

/*********************************************************************
 * Base statement parsers
 *********************************************************************/

// stmt: simple_stmt | compound_stmt
named_args!(pub statement(first_indent: usize, indent: usize) <CompleteStr, Vec<Statement>>,
  alt!(
    call!(compound_stmt, first_indent, indent) => { |stmt| vec![Statement::Compound(Box::new(stmt))] }
  | call!(simple_stmt, first_indent)
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
    expr_stmt
  | del_stmt => { |atoms| Statement::Del(atoms) }
  | pass_stmt
  | flow_stmt
  | import_stmt
  | global_stmt
  | nonlocal_stmt
  | assert_stmt
  )
);

/*********************************************************************
 * Expression statements
 *********************************************************************/

// expr_stmt: testlist_star_expr (annassign | augassign (yield_expr|testlist) |
//                     ('=' (yield_expr|testlist_star_expr))*)
// annassign: ':' test ['=' test]
named!(expr_stmt<CompleteStr, Statement>,
  do_parse!(
    lhs: testlist_star_expr >>
    r: ws2!(alt!(
      // Case 1: foo = bar
      do_parse!(
        rhs: many1!(ws2!(preceded!(char!('='), alt!(
          call!(ExpressionParser::<NewlinesAreNotSpaces>::yield_expr) => { |e| vec![e] }
        | testlist_star_expr
        )))) >> (
          Statement::Assignment(lhs.clone(), rhs)
        )
      )

      // Case 2: foo: bar = baz
    | do_parse!(
        char!(':') >>
        typed: call!(ExpressionParser::<NewlinesAreNotSpaces>::test) >>
        char!('=') >>
        rhs: call!(ExpressionParser::<NewlinesAreNotSpaces>::test) >> (
          Statement::TypedAssignment(lhs.clone(), *typed, vec![*rhs])
        )
      )

      // Case 3: Foo += bar (and other operators)
    | do_parse!(
        op: augassign >>
        rhs: alt!(
          call!(ExpressionParser::<NewlinesAreNotSpaces>::yield_expr) => { |e| vec![e] }
        | call!(ExpressionParser::<NewlinesAreNotSpaces>::testlist)
        ) >> (
          Statement::AugmentedAssignment(lhs, op, rhs)
        )
      )
    )) >>
    (r)
  )
);

// testlist_star_expr: (test|star_expr) (',' (test|star_expr))* [',']
named!(testlist_star_expr<CompleteStr, Vec<Expression>>,
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
named!(augassign<CompleteStr, AugAssignOp>,
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
  | preceded!(
      tuple!(tag!("return"), space_sep2),
      ws2!(call!(ExpressionParser::<NewlinesAreNotSpaces>::possibly_empty_testlist))
    ) => { |e| Statement::Return(e) }
  | raise_stmt
  | call!(ExpressionParser::<NewlinesAreNotSpaces>::possibly_empty_testlist)
    => { |e| Statement::Expressions(e) }
  )
);

// raise_stmt: 'raise' [test ['from' test]]
named!(raise_stmt<CompleteStr, Statement>,
  do_parse!(
    tag!("raise") >>
    t: opt!(tuple!(
      preceded!(space_sep2, call_test!()),
      opt!(preceded!(tuple!(space_sep2, tag!("from"), space_sep2), call_test!()))
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
named!(import_stmt<CompleteStr, Statement>,
  alt!(
    import_name => { |i| Statement::Import(i) }
  | import_from => { |i| Statement::Import(i) }
  )
);

// import_name: 'import' dotted_as_names
named!(import_name<CompleteStr, Import>,
  map!(preceded!(tuple!(tag!("import"), space_sep2), call!(ImportParser::<NewlinesAreNotSpaces>::dotted_as_names)),
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
      Import::ImportFrom { leading_dots, path, names }
    })
  )
);

pub(crate) struct ImportParser<ANS: AreNewlinesSpaces> {
    _phantom: PhantomData<ANS>,
}

impl<ANS: AreNewlinesSpaces> ImportParser<ANS> {

// import_as_name: NAME ['as' NAME]
named!(import_as_name<CompleteStr, (Name, Option<Name>)>,
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
named!(dotted_as_name<CompleteStr, (Vec<Name>, Option<Name>)>,
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
named!(import_as_names<CompleteStr, Vec<(Name, Option<Name>)>>,
  terminated!(
    separated_nonempty_list!(tuple!(spaces!(), char!(','), spaces!()), call!(Self::import_as_name)),
    opt!(tuple!(spaces!(), char!(','), spaces!()))
  )
);

// dotted_as_names: dotted_as_name (',' dotted_as_name)*
named!(dotted_as_names<CompleteStr, Vec<(Vec<Name>, Option<Name>)>>,
  separated_nonempty_list!(tuple!(spaces!(), char!(','), spaces!()), call!(Self::dotted_as_name))
);

// dotted_name: NAME ('.' NAME)*
named!(pub dotted_name<CompleteStr, Vec<Name>>,
  separated_nonempty_list!(tuple!(spaces!(), char!('.'), spaces!()), name)
);

} // end ImportParser

/*********************************************************************
 * Blocks
 *********************************************************************/

// suite: simple_stmt | NEWLINE INDENT stmt+ DEDENT
named_args!(pub block(indent: usize) <CompleteStr, Vec<Statement>>,
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
    | call!(try_stmt, indent)
    | call!(with_stmt, indent)
    | call!(decorated, indent) // Also takes care of funcdef, classdef, and ASYNC funcdef
    )
  )
);

// async_stmt: ASYNC (funcdef | with_stmt | for_stmt)
// taken care of in other parsers

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
    async: opt!(tuple!(tag!("async"), space_sep2)) >>
    tag!("for") >>
    space_sep2 >>
    item: call!(ExpressionParser::<NewlinesAreNotSpaces>::exprlist) >>
    space_sep2 >>
    tag!("in") >>
    space_sep2 >>
    iterator: call!(ExpressionParser::<NewlinesAreNotSpaces>::exprlist) >>
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
named_args!(try_stmt(indent: usize) <CompleteStr, CompoundStatement>,
  do_parse!(
    tag!("try") >>
    ws2!(char!(':')) >>
    try_block: call!(block, indent) >>
    except_clauses: many0!(do_parse!(
      newline >>
      count!(char!(' '), indent) >> 
      tag!("except") >>
      space_sep2 >>
      catch_what: call!(ExpressionParser::<NewlinesAreNotSpaces>::test) >>
      catch_as: opt!(preceded!(tuple!(space_sep2, tag!("as"), space_sep2), name)) >>
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
named_args!(with_stmt(indent: usize) <CompleteStr, CompoundStatement>,
  do_parse!(
    tag!("with") >>
    space_sep2 >>
    contexts: separated_nonempty_list!(ws2!(char!(',')), do_parse!(
      context: call!(ExpressionParser::<NewlinesAreNotSpaces>::expr) >>
      as_: opt!(preceded!(
        tuple!(space_sep2, tag!("as"), space_sep2), 
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
            CompoundStatement::For {
                async: false,
                item: vec![Expression::Name("foo".to_string())],
                iterator: vec![Expression::Name("bar".to_string())],
                for_block: vec![
                    Statement::Del(vec!["baz".to_string()])
                ],
                else_block: None
            }
        )));
    }

    #[test]
    fn test_for_else() {
        assert_eq!(compound_stmt(CS("for foo in bar:\n del baz\nelse:\n del qux"), 0, 0), Ok((CS(""),
            CompoundStatement::For {
                async: false,
                item: vec![Expression::Name("foo".to_string())],
                iterator: vec![Expression::Name("bar".to_string())],
                for_block: vec![
                    Statement::Del(vec!["baz".to_string()])
                ],
                else_block: Some(
                    vec![
                        Statement::Del(vec!["qux".to_string()])
                    ]
                )
            }
        )));
    }

    #[test]
    fn test_raise() {
        assert_eq!(small_stmt(CS("raise")), Ok((CS(""),
            Statement::Raise
        )));

        assert_eq!(small_stmt(CS("raise exc")), Ok((CS(""),
            Statement::RaiseExc(
                Expression::Name("exc".to_string()),
            )
        )));

        assert_eq!(small_stmt(CS("raise exc from exc2")), Ok((CS(""),
            Statement::RaiseExcFrom(
                Expression::Name("exc".to_string()),
                Expression::Name("exc2".to_string()),
            )
        )));
    }

    #[test]
    fn test_assign() {
        assert_eq!(small_stmt(CS("foo = bar")), Ok((CS(""),
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

        assert_eq!(small_stmt(CS("foo = bar = baz")), Ok((CS(""),
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
        assert_eq!(small_stmt(CS("foo:bar = baz")), Ok((CS(""),
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
        assert_eq!(small_stmt(CS("foo, bar = baz, qux")), Ok((CS(""),
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

        assert_eq!(small_stmt(CS("foo = bar = baz")), Ok((CS(""),
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
        assert_eq!(with_stmt(CS("with foo:\n del bar"), 0), Ok((CS(""),
            CompoundStatement::With(
                vec![
                    (Expression::Name("foo".to_string()), None),
                ],
                vec![
                    Statement::Del(vec!["bar".to_string()])
                ],
            )
        )));

        assert_eq!(with_stmt(CS("with foo as bar:\n del baz"), 0), Ok((CS(""),
            CompoundStatement::With(
                vec![
                    (Expression::Name("foo".to_string()), Some(Expression::Name("bar".to_string()))),
                ],
                vec![
                    Statement::Del(vec!["baz".to_string()])
                ],
            )
        )));
    }

    #[test]
    fn test_try() {
        assert_eq!(try_stmt(CS("try:\n del foo\nexcept Bar:\n del baz"), 0), Ok((CS(""),
            CompoundStatement::Try(Try {
                try_block: vec![
                    Statement::Del(vec!["foo".to_string()]),
                ],
                except_clauses: vec![
                    (
                        Expression::Name("Bar".to_string()),
                        None,
                        vec![Statement::Del(vec!["baz".to_string()])],
                    ),
                ],
                last_except: vec![],
                else_block: vec![],
                finally_block: vec![],
            })
        )));

        assert_eq!(try_stmt(CS("try:\n del foo\nexcept:\n del baz"), 0), Ok((CS(""),
            CompoundStatement::Try(Try {
                try_block: vec![
                    Statement::Del(vec!["foo".to_string()]),
                ],
                except_clauses: vec![],
                last_except: vec![
                    Statement::Del(vec!["baz".to_string()]),
                ],
                else_block: vec![],
                finally_block: vec![],
            })
        )));

        assert_eq!(try_stmt(CS("try:\n del foo\nelse:\n del baz"), 0), Ok((CS(""),
            CompoundStatement::Try(Try {
                try_block: vec![
                    Statement::Del(vec!["foo".to_string()]),
                ],
                except_clauses: vec![],
                last_except: vec![],
                else_block: vec![
                    Statement::Del(vec!["baz".to_string()]),
                ],
                finally_block: vec![],
            })
        )));

        assert_eq!(try_stmt(CS("try:\n del foo\nfinally:\n del baz"), 0), Ok((CS(""),
            CompoundStatement::Try(Try {
                try_block: vec![
                    Statement::Del(vec!["foo".to_string()]),
                ],
                except_clauses: vec![],
                last_except: vec![],
                else_block: vec![],
                finally_block: vec![
                    Statement::Del(vec!["baz".to_string()]),
                ],
            })
        )));
    }

}
