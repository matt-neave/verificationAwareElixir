use std::fs;
use pest::Parser;
use pest_derive::Parser;
use pest::iterators::Pair;
use pest::iterators::Pairs;

#[derive(Parser)]
#[grammar = "elixir_ast_v1.pest"]
pub struct ASTParser;

fn main() {
    let path = "./simple_ast.txt";
    let file_content = fs::read_to_string(path)
        .expect(format!("Failed to read {}", path).as_str());


    let test_ast = ASTParser::parse(Rule::condensed_list, "'hello'");
    println!("{:?}", test_ast);

    let prog_ast = ASTParser::parse(Rule::defmodule, file_content.as_str());
    println!("{:?}", prog_ast);
}


