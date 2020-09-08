extern crate python_parser;

use python_parser::ast::*;
use python_parser::*;

#[test]
fn assign_listcomp() {
    let (rest, ast) = file_input(make_strspan("foo = [bar for baz in qux]")).unwrap();
    assert_eq!(rest.fragment.0, "");
    assert_eq!(
        ast,
        vec![Statement::Assignment(
            vec![Expression::Name("foo".to_string()),],
            vec![vec![Expression::ListComp(
                Box::new(SetItem::Unique(Expression::Name("bar".to_string()))),
                vec![ComprehensionChunk::For {
                    async: false,
                    item: vec![Expression::Name("baz".to_string())],
                    iterator: Expression::Name("qux".to_string()),
                }]
            )]]
        )]
    );
}
