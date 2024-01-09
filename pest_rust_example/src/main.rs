use std::fs;
use pest::Parser;
use pest_derive::Parser;
use pest::iterators::Pair;
use pest::iterators::Pairs;

#[derive(Parser)]
#[grammar = "atom.pest"]
pub struct ASTParser;

fn main() {
    let path = "./simple_ast.txt";
    let file_content = fs::read_to_string(path)
        .expect(format!("Failed to read {}", path).as_str());

    let prog_ast = ASTParser::parse(Rule::ast, file_content.as_str())
        .expect("Pest failed to parse")
        .next()        // continue after the expect
        .unwrap()      // rust thing
        .into_inner(); // Move into the first Rule::tuple from the Rule::ast


    let prog_ast_iterator = prog_ast.clone();
    // pair.as_rule() to get the rule type i.e. Rule::ast 
    // pair.into_inner() to continue inwards
    // pair is the current level of the ast
    for _pair in prog_ast_iterator {
        continue;
    }

    // for example, if pair.as_rule() == Rule::tuple, then into_inner is of type Pairs (3 tuple components)    
    parse_tuple(prog_ast);
}

// Parse a top level AST
fn parse_tuple(mut tuple: Pairs<Rule>) {
    // Extract the Pairs from the tuple
    let mut tuple = tuple.next().unwrap().into_inner();
    let elem_1 = tuple.next().unwrap();
    let _elem_2 = tuple.next().unwrap();
    let _elem_3 = tuple.next().unwrap();

    match elem_1.as_rule() {
        Rule::ast_identifier => parse_ast_identifier(elem_1),
        _ => println!("Failed to match!"),
    };
}

fn parse_ast_identifier(ast_identifier: Pair<Rule>) {
    // println!("{}", ast_identifier.into_inner().as_str());
    let ast_identifier = ast_identifier.into_inner().next().unwrap();
    let result = match ast_identifier.as_rule() {
        Rule::atom => parse_atom(ast_identifier),
        _ => {
            println!("Failed to match!");
            "Err"
        },
    };
    println!("Result is {}", result);
}

fn parse_atom(atom: Pair<Rule>) -> &str {
    return atom.as_str();
}

