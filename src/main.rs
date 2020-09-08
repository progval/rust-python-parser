extern crate python_parser;

use std::env::args_os;
use std::fs::File;
use std::io::Read;

use python_parser::visitors::printer::format_module;
use python_parser::{file_input, make_strspan};

fn main() {
    let mut iter = args_os();
    iter.next();
    for filename in iter {
        let mut file = File::open(filename).expect("Could not open file");
        let mut content = String::new();
        file.read_to_string(&mut content)
            .expect("Could not read file");
        let (rest, ast) = file_input(make_strspan(&content)).unwrap();
        //println!("{:?}", ast);
        let output = format_module(&ast);
        if rest.fragment.0.len() > 0 {
            println!("\nUnparsed: {:?}\n\n", rest.fragment.0)
        }
        println!("{}", output);
    }
}
