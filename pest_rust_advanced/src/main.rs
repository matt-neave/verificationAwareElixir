use std::fs;
use pest::Parser;
use pest_derive::Parser;
use pest::iterators::Pair;

#[derive(Parser)]
#[grammar = "elixir_ast_v1.pest"]
pub struct ASTParser;

fn main() {
    let path = "./simple_ast.txt";
    let file_content = fs::read_to_string(path)
        .expect(format!("Failed to read {}", path).as_str());

    let prog_ast = ASTParser::parse(Rule::defmodule, file_content.as_str())
        .expect("Failed to parse the AST")
        .next()
        .unwrap();
    
    // let test = ASTParser::parse(Rule::r#tuple, "{{:., [], [{:__aliases__, [alias: false], [:IO]}, :puts]}, [], [\"Hello\"]}")
    //     .expect("Couldnt parse")
    //     .next()
    //     .unwrap();
    // println!("{}", test);

    // Match prog_ast on Rule::defmodule
    // prog_ast.into_inner() returns [comma, metadata, comma, alias, comma, do block]
    parse_defmodule(prog_ast);
}

pub fn parse_defmodule(ast_node: Pair<Rule>) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::do_block => parse_do_block(pair),
            _              => (),
        };
    }
}

pub fn parse_do_block(ast_node: Pair<Rule>) {
    // Do block contains multiple statements in it's arguments

    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block => parse_block(pair),
            _           => (),
        };
    }
}

pub fn parse_block(ast_node: Pair<Rule>) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block_statements => parse_block_statements(pair),
            _                      => (),
        };
    }
    
}

pub fn parse_block_statements(ast_node: Pair<Rule>) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block_statement => parse_block_statement(pair),
            _                     => (),
        }
    }
}

pub fn parse_block_statement(ast_node: Pair<Rule>) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::function_definition => parse_function_definition(pair),
            _                         => (),
        }
    }
}

pub fn parse_function_definition(ast_node: Pair<Rule>) {
    println!("{}\n", ast_node);
}