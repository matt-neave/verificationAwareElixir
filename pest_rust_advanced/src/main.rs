use std::f32::consts::E;
use std::fs;
use std::env;
use std::num;
use pest::Parser;
use pest_derive::Parser;
use pest::iterators::Pair;

// Logging
use log::trace;
use log::debug;
use log::info;
use log::warn;
use log::error;
use log::Level;

use log::LevelFilter;
use env_logger::fmt::Color;

use std::io::Write;

mod internal_representation;
use internal_representation::formatted_condition;

#[path = "macros/parse_macros.rs"]
#[macro_use]
mod parse_macros;

#[derive(Parser)]
#[grammar = "elixir_ast_v1.pest"]
pub struct ASTParser;

fn main() {
    let args: Vec<String> = env::args().collect();
    let default_path = "./distributed_ast.txt";

    let path = if args.len() > 1 {
        &args[1]
    } else {
        default_path
    };

    // Initialise logger
    env_logger::builder()
        .format(|buf, record| {
            let level = record.level();
            let mut style = buf.style();
            match record.level() {
                Level::Error => style.set_color(Color::Red),
                Level::Warn => style.set_color(Color::Yellow),
                Level::Info => style.set_color(Color::Green),
                Level::Debug => style.set_color(Color::Blue),
                Level::Trace => style.set_color(Color::Cyan),
            };

            writeln!(
                buf,
                "{}:{} [{}] - {}",
                record.file().unwrap_or("unknown"),
                record.line().unwrap_or(0),
                style.value(level),
                record.args()
            )
        })
        .filter_level(LevelFilter::Trace)
        .init();

    let file_content = fs::read_to_string(path)
        .expect(format!("Failed to read {}", path).as_str());

    let prog_ast = ASTParser::parse(Rule::elixir_program, file_content.as_str())
        .expect("Failed to parse the AST")
        .next()
        .unwrap();
    
    let mut writer = internal_representation::file_writer::FileWriter::new("test_out.txt").unwrap();

    parse_program(prog_ast, &mut writer);

    writer.commit().expect("Failed to commit to file");
}

pub fn parse_program(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::defmodule => parse_defmodule(pair, file_writer),
            Rule::block     => parse_block(pair, file_writer, false, false),
            _ => parse_warn!("program", pair.as_rule()),
        }
    }
}

pub fn parse_defmodule(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::r#do       => parse_do(pair, file_writer, false, false),
            Rule::metadata   => (),
            Rule::alias_name => (),
            _                => parse_warn!("defmodule", pair.as_rule()),
        };
    }
}

pub fn parse_do_block(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
    func_def: bool
) {
    // Do block contains multiple statements in it's arguments
    // The last statement is also returned
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block => parse_block(pair, file_writer, ret, func_def),
            _           => parse_warn!("do block", pair.as_rule()),
        };
    }
}

pub fn parse_block(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
    func_def: bool
) {
    let mut inner_iter = ast_node.into_inner().peekable();

    while let Some(pair) = inner_iter.next() {
        let last = inner_iter.peek().is_none();
        match pair.as_rule() {
            Rule::block_statements => {
                parse_block_statements(pair, file_writer, (last && func_def) || ret);
            },
            _ => parse_warn!("block", pair.as_rule()),
        }
    }
}


pub fn parse_block_statements(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter, ret: bool) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block_statement => parse_block_statement(pair, file_writer, ret),
            _                     => parse_warn!("block statements", pair.as_rule()),
        }
    }
}

pub fn parse_block_statement(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter, ret: bool) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::function_definition => parse_function_definition(pair, file_writer, ret),
            Rule::defmodule           => parse_defmodule(pair, file_writer),
            Rule::tuple               => parse_tuple(pair, file_writer, ret),
            Rule::assignment          => parse_assignment(pair, file_writer, ret),
            Rule::send                => parse_send(pair, file_writer, ret),
            _                         => parse_warn!("block statement", pair.as_rule()),
        }
    }
}

fn parse_send(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool
) {
    let mut send_target = None;
    let mut send_arguments = None;
    let mut send_tupled_arguments = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::atom                 => send_target = Some(pair),
            Rule::function_arguments   => send_arguments = Some(pair),
            Rule::tuple                => send_tupled_arguments = Some(pair),
            _                          => parse_warn!("send", pair.as_rule()),
        }
    }

    // Create a vector of tuples of argument types and identifiers
    let send_args = extract_send_arguments(send_arguments, send_tupled_arguments);

    // Write the send to the file
    if let Some(x) = send_target {
        file_writer.write_send(x.as_str(), send_args);
    } else {
        panic!("No send target in send expression");
    }
}

fn extract_send_arguments<'a>(send_arguments: Option<Pair<'a, Rule>>, send_tupled_arguments: Option<Pair<'a, Rule>>) -> Vec<&'a str> {
    let mut send_args = Vec::new();
    if let Some(x) = send_arguments {
        for pair in x.into_inner() {
            send_args.push(pair.as_str());
        }
    } else if let Some(x) = send_tupled_arguments {
        for pair in x.into_inner() {
            send_args.push(pair.as_str());
        }
    }
    send_args
}

fn get_variable_name(ast_node: Pair<Rule>) -> String {
    if ast_node.as_rule() != Rule::assigned_variable {
        panic!("Can't get variable name unless type assigned_variable");
    }
    if let Some(x) = ast_node.into_inner().find(|y| y.as_rule() == Rule::atom) {
        return x.as_str().replace(":", "");
    } else {
        panic!("No atom in assigned variable");
    }
}

fn parse_assignment(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter, ret: bool) {
    let mut assigned_variable = None;
    let mut expression = None;

    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::assigned_variable   => assigned_variable = Some(pair),
            Rule::expression_argument => expression = Some(pair),
            _                         => (),
        }
    }
    if let Some(x) = assigned_variable {
        let variable_name = get_variable_name(x);
        file_writer.write_assignment_variable(&*variable_name);
    } else {
        panic!("No variable name in assignment expression");
    }
    if let Some(x) = expression {
        parse_expression_tuple(x, file_writer, ret);
    } else {
        panic!("No expression in assignment expression");
    }
}

fn get_function_name(ast_node: Pair<Rule>, str_out: &mut String) {
    // TODO return the function name from the node
    str_out.push_str(ast_node.as_str());
    str_out.remove(0);
}

fn argument_list_as_str(argument_list: Pair<Rule>) -> String {
    let mut out = String::from("");
    for argument in argument_list.into_inner() {
        for pair in argument.into_inner() {
            if pair.as_rule() == Rule::atom {
                let mut x: String = String::from(pair.as_str());
                x = x[1..].to_string();
                out += x.as_str();
                out += ",";
            }
        }
    }
    out.pop();
    out
}

fn get_symbol_type(
    type_node: Pair<Rule>
) -> internal_representation::sym_table::SymbolType {
    match type_node.as_str() {
        ":integer" => internal_representation::sym_table::SymbolType::Integer,
        ":string"  => internal_representation::sym_table::SymbolType::String,
        ":bool"    => internal_representation::sym_table::SymbolType::Boolean,
        _          => internal_representation::sym_table::SymbolType::Integer,
    }
}

fn create_function_symbol_table(
    args: &str, 
    type_spec: Pair<Rule>
) -> internal_representation::sym_table::SymbolTable {
    let mut sym_table = internal_representation::sym_table::SymbolTable::new();

    let mut return_type: Option<Pair<Rule>> = None;
    let mut argument_types: Option<Pair<Rule>> = None;
    for pair in type_spec.into_inner() {
        match pair.as_rule() {
            Rule::argument_type           => return_type = Some(pair),
            Rule::function_arguments_type => argument_types = Some(pair), 
            _                             => parse_warn!("create function symbol table", pair.as_rule()),
        }
    }

    if let Some(x) = return_type {
        sym_table.add_entry("RET_V".to_string(), get_symbol_type(x));
    }

    let args_v: Vec<&str> = args.trim_matches(|c| c == '[' || c == ']').split(',').map(|s| s.trim()).collect();

    if let Some(x) = argument_types.clone().expect("no argument types").into_inner().find(|y| y.as_rule() == Rule::argument_types) {
        let mut i = 0;
        for pair in x.into_inner() {
            sym_table.add_entry(args_v.get(i).expect("arguments and types size misalign").to_string(), get_symbol_type(pair));
            i += 1;
        }
    } else {
        panic!("no argument types");
    }

    sym_table.pretty_print();
    sym_table
}

pub fn parse_function_definition(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
) {
    // Write a new function name to the output file
    let mut func_name = String::new();
    // [function_name, metadata, arguments, do]
    let mut func_name_node: Option<Pair<Rule>> = None;
    let mut func_body_node: Option<Pair<Rule>> = None;
    let mut func_arg_node: Option<Pair<Rule>> = None;
    let mut func_type_spec: Option<Pair<Rule>> = None;
    let mut _func_metadata_node: Option<Pair<Rule>> = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::function_name      => func_name_node = Some(pair), 
            Rule::function_arguments => func_arg_node = Some(pair),
            Rule::r#do               => func_body_node = Some(pair),
            Rule::metadata           => _func_metadata_node = Some(pair),
            Rule::type_spec          => func_type_spec = Some(pair),
            _                        => parse_warn!("function definition", pair.as_rule()),
        }
    }
    
    get_function_name(func_name_node.unwrap(), &mut func_name);
    let args = &*argument_list_as_str(func_arg_node.expect("no function arguments"));
    let mut sym_table;
    if let Some(x) = func_type_spec {
        sym_table = create_function_symbol_table(args, x);
    } else {
        sym_table = internal_representation::sym_table::SymbolTable::new();
        error!("Missing type spec for function {}.", func_name);
    }
    file_writer.new_function(&*func_name, args, sym_table);
    
    // Write the body 
    // Start by setting up the channels
    // Use predefiend code blocks for send and recv
    parse_do(func_body_node.unwrap(), file_writer, ret, true);

    // Close the function 
    file_writer.commit_function();
    // file_writer.commit().expect("Failed to commit to file");
}

// fn parse_function_body(
//     ast_node: Pair<Rule>, 
//     file_writer: &mut internal_representation::file_writer::FileWriter, ret: bool,
// ) {
//     for pair in ast_node.into_inner() {
//         match pair.as_rule() {
//             Rule::r#do        => parse_do(pair, file_writer, ret),
//             Rule::r#do_single => parse_do_single(pair, file_writer, ret),
//             Rule::r#do_block  => parse_do_block(pair, file_writer, ret),
//             _                 => println!("{}", pair),
//         } 
//     }
// }

fn parse_do(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
    func_def: bool,    
) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::do_single => parse_do_single(pair, file_writer, ret, func_def),
            Rule::do_block  => parse_do_block(pair, file_writer, ret, func_def),
            _               => parse_warn!("do", pair.as_rule()), 
           }
    }
}

fn parse_do_single(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
    func_def: bool
) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::tuple           => parse_tuple(pair, file_writer, ret || func_def),
            Rule::block_statement => parse_block_statement(pair, file_writer, ret),
            _                     => parse_warn!("do single", pair.as_rule()), 
           }
    }
}

fn parse_tuple(    
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
) {
    // Given a tuple does not begin with an identified keyword i.e.
    // is an "atom", we assume it is a function call
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::expression_tuple    => parse_expression_tuple(pair, file_writer, ret),  
            Rule::binary_operation    => parse_binary_operation(pair, file_writer, ret),
            Rule::r#if                => parse_if(pair, file_writer, ret),
            Rule::function_definition => parse_function_definition(pair, file_writer, ret),
            Rule::metadata            => (),
            _                         => parse_warn!("tuple", pair.as_rule()),
        }
    }
}

/// Converts a tuple argument into a string representation
/// For now, only support negative numbers
/// TODO: support all expression types and do blocks
fn resolve_tuple_argument(ast_node: Pair<Rule>) -> &str {
    panic!("TODO implement tuple arguments");
    ""
}

fn resolve_negative_number(ast_node: Pair<Rule>) -> &str {
    println!("{}", ast_node);
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::number => {
                let s = format!("-{}", pair.as_str());
                return Box::leak(s.into_boxed_str());
            },
            _ => () 
        }
    }
    ""
}

/// Takes an 'argument', likely to be an expression string and parses it as a string
/// by applying the operations on the operators recursively
/// returns a string representation of a list of arguments
fn parse_call_arguments(ast_node: Pair<Rule>) -> String {
    let mut out = String::from("[");
    for pair in ast_node.into_inner() {
        for arg in pair.into_inner() {
            let arg_s = match arg.as_rule() {
                Rule::r#number => arg.as_str(),
                Rule::r#string => arg.as_str(),
                Rule::negative_number => resolve_negative_number(arg),
                Rule::tuple    => resolve_tuple_argument(arg),
                _ => panic!("Failed to find argument in argument list"),
            };
            out.push_str(arg_s);
            out.push_str(",");
        }
    }
    out.pop();
    out.push_str("]");
    out
}

fn parse_expression_tuple(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,    
) {
    let mut io_node: Option<Pair<Rule>> = None;
    let mut atom_node: Option<Pair<Rule>> = None;
    let mut arguments_node: Option<Pair<Rule>> = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::io                   => io_node = Some(pair), 
            Rule::atom                 => atom_node = Some(pair),
            Rule::expression_arguments => arguments_node = Some(pair),
            Rule::spawn_process        => parse_spawn_process(pair, file_writer, ret),
            _                          => parse_warn!("expression tuple", pair.as_rule()),
        }
    }

    if let Some(x) = io_node {
        println!("io match: {}\n", x.as_str());
    }

    if let Some(x) = atom_node {
        let mut func_name = x.as_str().to_string();
        func_name.remove(0);
        if let Some(arguments) = arguments_node {
            println!("{}", arguments.as_str());
            let call_args = parse_call_arguments(arguments);
            file_writer.write_function_call(&*func_name, &call_args, "" /* TODO, replace with var name if assignment */, ret);
        } else {
            file_writer.write_function_call(&*func_name, "", "", ret);
        }
    }

}

fn parse_spawn_process(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool
) {
    let mut process_type = None;
    let mut process_arguments = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::atom                 => process_type = Some(pair),
            Rule::function_arguments   => process_arguments = Some(pair),
            _                          => parse_warn!("spawn process", pair.as_rule())
        }
    }

    // TODO: refactor nesting
    if let Some(x) = process_type {
        if let Some(y) = process_arguments {
            let args = &*argument_list_as_str(y);
            file_writer.write_spawn_process(&*x.as_str().replace(":", ""), args);
        } else {
            panic!("No process type provided in spawn");
        }        
    } else {
        panic!("No process type provided in spawn");
    }

}

fn parse_if(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool
) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::conditions => parse_conditions(pair, file_writer, ret),
            _                => parse_warn!("if", pair.as_rule()),
        }
    }
}

fn create_condition(
    ast_node: Pair<Rule>
) -> internal_representation::formatted_condition::FormattedCondition {
    // Base case, we find a primitive
    if let Some(condition) = ast_node.clone().into_inner().find(|x| x.as_rule() == Rule::primitive) {
        return internal_representation::formatted_condition::FormattedCondition::Primitive(condition.to_string());
    }

    // Recursive case, we find a tuple
    // Either the tuple if a conjuncton / disjunction (and / or)
    // Or the tuple is an operation (expression_tuple)
    else if let Some(condition) = ast_node.clone().into_inner().find(|a| a.as_rule() == Rule::or) {
        // Recurse left
        let Some(l_condition) = condition.clone().into_inner().find(|a| a.as_rule() == Rule::if_condition) else { todo!() };
        let l_expr = create_condition(l_condition);
        
        // Recurse right
        let Some(r_condition) = condition.clone().into_inner().find(|a| a.as_rule() == Rule::if_condition) else { todo!() };
        let r_expr = create_condition(r_condition);

        // Return new FormattedCondition
        return internal_representation::formatted_condition::FormattedCondition::BinaryOperation(&"or", Box::new(l_expr), Box::new(r_expr));
    }
    // else if let Some(y) = x.clone().into_inner().find(|a| a.as_rule() == Rule::expression_tuple) {
        // println!("Expression tuple");
    // }
    else if ast_node.as_rule() == Rule::if_condition {
        // Recurse into the condition
        // Could be { not | or | and | true | false | boolean_expression | primitive }
        for pair in ast_node.into_inner() {
            match pair.as_rule() {
                Rule::r#bool => return create_condition(pair),
                _            => todo!(),
            };
        };
    }
    else if ast_node.as_rule() == Rule::bool {
        match ast_node.as_str() {
            "true"  => return internal_representation::formatted_condition::FormattedCondition::Boolean(true),
            "false" => return internal_representation::formatted_condition::FormattedCondition::Boolean(false),             
            _       => (),
        }
    }   
    else {
        println!("{}", ast_node);
        println!("{}", ast_node.as_str());
        panic!("Failed to parse if condition");
    }

    internal_representation::formatted_condition::FormattedCondition::Number(1)
} 

fn parse_conditions(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool
) {
    // TODO write the translation for conditions
    let mut do_block: Option<Pair<Rule>> = None;
    let mut do_else_block: Option<Pair<Rule>> = None;
    let mut condition: Option<Pair<Rule>> = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::if_condition         => condition = Some(pair), 
            Rule::r#do                 => do_block = Some(pair),
            Rule::do_else              => do_else_block = Some(pair),
            _                          => parse_warn!("conditions", pair.as_rule()),
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
        parse_do(x, file_writer, ret, false);
        file_writer.commit_if();
        return;
    }
    
    // If required, write the else
    let do_else_block = do_else_block       
        .unwrap_or_else(|| panic!("No do or do else in if"));

    let mut do_else_block = do_else_block.into_inner();
    if let Some(pair) = do_else_block.next() {
        match pair.as_rule() {
            Rule::tuple     => parse_tuple(pair, file_writer, ret),
            Rule::primitive => parse_primitive(pair, file_writer, ret),
            _               => parse_warn!("conditions", pair.as_rule()),
        }            
    }
    file_writer.write_else();
    
    if let Some(pair) = do_else_block.next() {
        match pair.as_rule() {
            Rule::tuple     => parse_tuple(pair, file_writer, ret),
            Rule::primitive => parse_primitive(pair, file_writer, ret),
            _               => parse_warn!("conditions", pair.as_rule()),
        }
    }
    file_writer.commit_if();
}

fn parse_primitive(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, ret: bool
) {
    file_writer.write_primitive(&*ast_node.as_str(), ret);
}

fn name_from_tuple_str(input: &str) -> &str {
    // Check if the input string starts with "{:" and ends with "}"
    if input.starts_with("{:") && input.ends_with("}") {
        // Remove leading "{:" and trailing "}"
        let content = &input[2..(input.len() - 1)];

        // Split the content into parts separated by commas
        let parts: Vec<&str> = content.split(',').map(|s| s.trim()).collect();

        // Check if there are at least two parts (name and other content)
        if parts.len() >= 2 {
            // Extract and return the name (the first part)
            return &parts[0];
        }
    }

    // Return None if the input doesn't match the expected format
    &"Failed translation"
}

fn parse_binary_operation(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool
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
    // TODO recursive function call to evaluate expression such as 1 + 1 + 1
    // i.e. {} {} {} operands[0], operator, operands[1]
    if let Some(x) = binary_operator {
        let operand_left = name_from_tuple_str(&*operands[0].as_str());
        let operand_right = name_from_tuple_str(&*operands[1].as_str());
        file_writer.write_operation(x.as_str(), operand_left, operand_right, ret);
    }
}
