extern crate python_parser;

use python_parser::*;
use python_parser::ast::*;

#[test]
fn test_call_and_attribute() {
    let (rest, ast) = file_input(make_strspan("egg = foo.bar().baz()")).unwrap();
    assert_eq!(rest.fragment.0, "");
    assert_eq!(ast, vec![
        Statement::Assignment(
            vec![
                Expression::Name("egg".to_string()),
            ],
            vec![
                vec![
                    Expression::Call(
                        Box::new(Expression::Attribute(
                            Box::new(Expression::Call(
                                Box::new(Expression::Attribute(
                                    Box::new(Expression::Name("foo".to_string())),
                                    "bar".to_string(),
                                )),
                                Arglist::default(),
                            )),
                            "baz".to_string(),
                        )),
                        Arglist::default(),
                    ),
                ],
            ],
        )
    ]);
}


#[test]
fn test_call_and_attribute2() {
    let (rest, ast) = file_input(make_strspan("egg = foo.bar(baz, qux)")).unwrap();
    assert_eq!(rest.fragment.0, "");
    assert_eq!(ast, vec![
        Statement::Assignment(
            vec![
                Expression::Name("egg".to_string()),
            ],
            vec![
                vec![
                    Expression::Call(
                        Box::new(Expression::Attribute(
                            Box::new(Expression::Name("foo".to_string())),
                            "bar".to_string(),
                        )),
                        Arglist {
                            positional_args: vec![
                                Argument::Normal(Expression::Name("baz".to_string())),
                                Argument::Normal(Expression::Name("qux".to_string())),
                            ],
                            keyword_args: vec![],
                        }
                    ),
                ],
            ],
        )
    ]);
}

