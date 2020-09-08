extern crate python_parser;

use python_parser::ast::*;
use python_parser::*;

#[test]
fn test_call_and_attribute() {
    let (rest, ast) = file_input(make_strspan("egg = foo.bar().baz()")).unwrap();
    assert_eq!(rest.fragment.0, "");
    assert_eq!(
        ast,
        vec![Statement::Assignment(
            vec![Expression::Name("egg".to_string()),],
            vec![vec![Expression::Call(
                Box::new(Expression::Attribute(
                    Box::new(Expression::Call(
                        Box::new(Expression::Attribute(
                            Box::new(Expression::Name("foo".to_string())),
                            "bar".to_string(),
                        )),
                        Vec::new(),
                    )),
                    "baz".to_string(),
                )),
                Vec::new(),
            ),],],
        )]
    );
}

#[test]
fn test_call_and_attribute2() {
    let (rest, ast) = file_input(make_strspan("egg = foo.bar(baz, qux)")).unwrap();
    assert_eq!(rest.fragment.0, "");
    assert_eq!(
        ast,
        vec![Statement::Assignment(
            vec![Expression::Name("egg".to_string()),],
            vec![vec![Expression::Call(
                Box::new(Expression::Attribute(
                    Box::new(Expression::Name("foo".to_string())),
                    "bar".to_string(),
                )),
                vec![
                    Argument::Positional(Expression::Name("baz".to_string())),
                    Argument::Positional(Expression::Name("qux".to_string())),
                ],
            ),],],
        )]
    );
}
