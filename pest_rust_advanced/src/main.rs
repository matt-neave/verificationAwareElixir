use std::fs;
use pest::Parser;
use pest_derive::Parser;
use pest::iterators::Pair;

mod internal_representation;
use internal_representation::formatted_condition;

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
            Rule::r#do       => parse_do(pair, file_writer),
            Rule::metadata   => (),
            Rule::alias_name => (),
            _                => println!("undefined1"),
        };
    }
}

pub fn parse_do_block(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter) {
    // Do block contains multiple statements in it's arguments

    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block => parse_block(pair, file_writer),
            _           => println!("undefined2"),
        };
    }
}

pub fn parse_block(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block_statements => parse_block_statements(pair, file_writer),
            _                      => println!("undefined3"),
        };
    }
    
}

pub fn parse_block_statements(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block_statement => parse_block_statement(pair, file_writer),
            _                     => println!("undefined4"),
        }
    }
}

pub fn parse_block_statement(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::function_definition => parse_function_definition(pair, file_writer),
            Rule::tuple               => parse_tuple(pair, file_writer),
            _                         => println!("undefined5"),
        }
    }
}

fn get_function_name(ast_node: Pair<Rule>, str_out: &mut String) {
    // TODO return the function name from the node
    str_out.push_str(ast_node.as_str());
    str_out.remove(0);
}

pub fn parse_function_definition(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter,
) {
    // Write a new function name to the output file
    let mut func_name = String::new();
    // [function_name, metadata, arguments, do]
    let mut func_name_node: Option<Pair<Rule>> = None;
    let mut func_body_node: Option<Pair<Rule>> = None;
    let mut _func_arg_node: Option<Pair<Rule>> = None;
    let mut _func_metadata_node: Option<Pair<Rule>> = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::function_name      => func_name_node = Some(pair), 
            Rule::function_arguments => _func_arg_node = Some(pair),
            Rule::r#do               => func_body_node = Some(pair),
            Rule::metadata           => _func_metadata_node = Some(pair),
            _                        => println!("undefined6"),
        }
    }
    
    get_function_name(func_name_node.unwrap(), &mut func_name);
    file_writer.new_function(&*func_name, None);
    

    // Write the body 
    // Start by setting up the channels
    // Use predefiend code blocks for send and recv
    parse_do(func_body_node.unwrap(), file_writer);

    // Close the function 
    file_writer.commit_function();
    file_writer.commit().expect("Failed to commit to file");
}

// fn parse_function_body(
//     ast_node: Pair<Rule>, 
//     file_writer: &mut internal_representation::file_writer::FileWriter,
// ) {
//     for pair in ast_node.into_inner() {
//         match pair.as_rule() {
//             Rule::r#do        => parse_do(pair, file_writer),
//             Rule::r#do_single => parse_do_single(pair, file_writer),
//             Rule::r#do_block  => parse_do_block(pair, file_writer),
//             _                 => println!("{}", pair),
//         } 
//     }
// }

fn parse_do(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter,    
) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::do_single => parse_do_single(pair, file_writer),
            Rule::do_block  => parse_do_block(pair, file_writer),
            _               => println!("undefined7"), 
           }
    }
}

fn parse_do_single(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter,
) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::tuple => parse_tuple(pair, file_writer),
            _           => println!("undefined8"), 
           }
    }
}

fn parse_tuple(    
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter,
) {
    // Given a tuple does not begin with an identified keyword i.e.
    // is an "atom", we assume it is a function call
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::expression_tuple    => parse_expression_tuple(pair, file_writer),  
            Rule::binary_operation    => parse_binary_operation(pair, file_writer),
            Rule::r#if                => parse_if(pair, file_writer),
            Rule::function_definition => parse_function_definition(pair, file_writer),
            Rule::metadata            => (),
            _                         => println!("undefined9"),
        }
    }
}

fn parse_expression_tuple(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter,    
) {
    let mut io_node: Option<Pair<Rule>> = None;
    let mut atom_node: Option<Pair<Rule>> = None;
    let mut arguments_node: Option<Pair<Rule>> = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::io                   => io_node = Some(pair), 
            Rule::atom                 => atom_node = Some(pair),
            Rule::expression_arguments => arguments_node = Some(pair),
            _                          => println!("undefined10"),
        }
    }

    if let Some(x) = io_node {
        println!("io match: {}\n", x.as_str());
    }

    if let Some(x) = atom_node {
        let mut func_name = x.as_str().to_string();
        func_name.remove(0);
        if let Some(arguments) = arguments_node {
            file_writer.write_function_call(&*func_name, &*arguments.as_str(), "val");
        } else {
            file_writer.write_function_call(&*func_name, "", "val");
        }
    }

}

fn parse_if(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter
) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::conditions => parse_conditions(pair, file_writer),
            _                => println!("undefined11"),
        }
    }
}

fn create_condition(
    ast_node: Pair<Rule>
) -> internal_representation::formatted_condition::FormattedCondition {
    internal_representation::formatted_condition::FormattedCondition::Number(1)
} 

fn parse_conditions(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter
) {
    // TODO write the translation for conditions
    let mut do_block: Option<Pair<Rule>> = None;
    let mut do_else_block: Option<Pair<Rule>> = None;
    let mut condition: Option<Pair<Rule>> = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::tuple                => condition = Some(pair), 
            Rule::r#do                 => do_block = Some(pair),
            Rule::do_else              => do_else_block = Some(pair),
            _                          => println!("undefined12"),
        }
    }

    // To do, reformat so that parse block returns the
    // list of instructions to write

    let condition = condition
        .unwrap_or_else(|| panic!("Unconditional if"));


    // Write the if statement
    let formatted_condition = create_condition(condition);
    file_writer.write_if_condition(formatted_condition);

    // Parse the do block
    if let Some(x) = do_block {
        parse_do(x, file_writer);
        file_writer.commit_if();
        return;
    }
    
    // If required, write the else
    let do_else_block = do_else_block       
        .unwrap_or_else(|| panic!("No do or do else in if"));

    let mut do_else_block = do_else_block.into_inner();
    if let Some(pair) = do_else_block.next() {
        println!("{}", pair);
        match pair.as_rule() {
            Rule::tuple     => parse_tuple(pair, file_writer),
            Rule::primitive => parse_primitive(pair, file_writer),
            _               => println!("undefined13"),
        }            
    }
    file_writer.write_else();
    
    if let Some(pair) = do_else_block.next() {
        match pair.as_rule() {
            Rule::tuple     => parse_tuple(pair, file_writer),
            Rule::primitive => parse_primitive(pair, file_writer),
            _               => println!("undefined13"),
        }
    }
    file_writer.commit_if();
}

fn parse_primitive(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter
) {
    file_writer.write_primitive(&*ast_node.as_str());
}

fn parse_binary_operation(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter
) {
    let mut binary_operator: Option<Pair<Rule>> = None;
    let mut operands: Vec<Pair<Rule>> = Vec::new();
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::binary_operator => binary_operator = Some(pair),
            Rule::tuple => operands.push(pair), // Use push() to add elements to the vector
            _ => println!(),
        }
    }

    // TODO order the binary operation
    // i.e. {} {} {} operands[0], operator, operands[1]
    if let Some(x) = binary_operator {
        file_writer.write_operation(x.as_str(), operands[0].as_str(), operands[1].as_str());
    } else {
        println!("oopsies");
    }
}
