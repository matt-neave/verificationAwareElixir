use std::fs;
use pest::Parser;
use pest_derive::Parser;
use pest::iterators::Pair;

mod internal_representation;

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
    
    let mut writer = internal_representation::file_writer::FileWriter::new("test_out.txt").unwrap();

    parse_defmodule(prog_ast, &mut writer);
}

pub fn parse_defmodule(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::do_block => parse_do_block(pair, file_writer),
            _              => (),
        };
    }
}

pub fn parse_do_block(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter) {
    // Do block contains multiple statements in it's arguments

    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block => parse_block(pair, file_writer),
            _           => (),
        };
    }
}

pub fn parse_block(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block_statements => parse_block_statements(pair, file_writer),
            _                      => (),
        };
    }
    
}

pub fn parse_block_statements(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block_statement => parse_block_statement(pair, file_writer),
            _                     => (),
        }
    }
}

pub fn parse_block_statement(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::function_definition => parse_function_definition(pair, file_writer),
            _                         => (),
        }
    }
}

fn get_function_name(ast_node: Pair<Rule>, str_out: &mut String) {
    // TODO return the function name from the node
    str_out.push_str(ast_node.as_str());
    str_out.remove(0);
}

pub fn parse_function_definition(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter) {
    println!("{}\n", ast_node);
    // Write a new function name to the output file
    let mut func_name = String::new();
    // [function_name, metadata, arguments, do]
    let mut func_name_node: Option<Pair<Rule>> = None;
    let mut _func_body_node: Option<Pair<Rule>> = None;
    let mut _func_arg_node: Option<Pair<Rule>> = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::function_name      => func_name_node = Some(pair), 
            Rule::function_arguments => _func_arg_node = Some(pair),
            Rule::r#do               => _func_body_node = Some(pair),
            _                        => (),
        }
    }
    
    get_function_name(func_name_node.unwrap(), &mut func_name);

    file_writer.writeln(&*format!("proctype {} {{", &*func_name));

    // Write the body

    // Close the function 
    file_writer.writeln("}");
    file_writer.commit().expect("Failed to commit to file");
}