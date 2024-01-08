use std::fs;
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "atom.pest"]
pub struct ASTParser;

fn main() {
    let path = "./simple_ast.txt";
    let file_content = fs::read_to_string(path)
        .expect(format!("Failed to read {}", path).as_str());

    // print!("Read file successfully\n{}\n", file_content);
    let successful_parse = ASTParser::parse(Rule::ast, file_content.as_str());
    println!("{:?}", successful_parse);

    // let successful_parse = ASTParser::parse(Rule::ast, "{:defmodule, [], [hello, hello]}");
    // println!("{:?}", successful_parse);
    

}


