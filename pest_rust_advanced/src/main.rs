use core::panic;
use regex::Regex;
use std::fs;
use std::process::Command;
use std::io::{Read, Write};
use std::path::Path;
use std::fs::File;

// Pest
use pest::Parser;
use pest_derive::Parser;
use pest::iterators::Pair;

// Logging
use log::warn;
use log::error;
use log::Level;

use log::LevelFilter;
use env_logger::fmt::Color;

mod internal_representation;
use internal_representation::{formatted_condition, sym_table, model_runner};

#[path = "macros/parse_macros.rs"]
#[macro_use]
mod parse_macros;

#[derive(Parser)]
#[grammar = "elixir_ast_v1.pest"]
pub struct ASTParser;

fn main() {
    let path = "./ast_output.txt";
    let model_path = "test_out.pml";

    let args = std::env::args().collect::<Vec<String>>();
    let model_check_flag = args.contains(&"--verify".to_string()) || args.contains(&"-v".to_string());
    let silent_flag = args.contains(&"--silent".to_string()) || args.contains(&"-s".to_string());

    extract_elixir_ast(path, silent_flag);
    init_logger(silent_flag);

    let file_content = fs::read_to_string(path)
        .unwrap_or_else(|_| panic!("Failed to read {}", path));

    let prog_ast = ASTParser::parse(Rule::elixir_program, file_content.as_str())
        .expect("Failed to parse the AST")
        .next()
        .unwrap();
    
    let mut writer = internal_representation::file_writer::FileWriter::new(&model_path).unwrap();

    if !silent_flag {
        println!("{}", prog_ast);
    }

    parse_program(prog_ast, &mut writer);

    writer.commit().expect("Failed to commit to file");

    if model_check_flag {
        model_runner::run_model(model_path);
    }
}

fn extract_elixir_ast(out_file: &str, silent: bool) {
    let arg_error = "Incorrect usage: cargo run -- \"target_file\"";
    let arg_binding = std::env::args().last().expect(arg_error);
    let dir = Path::new(&arg_binding);
    // TODO this could be a file now... can parse the target file as arg to mix
    let ast_extractor_code = &*format!("defmodule AstExtractor do
  def main do
    {{:ok, ast}} = Code.string_to_quoted(File.read!(\"../{}\"))
    File.write!(\"../{}\", inspect(ast, limit: :infinity)) # Writing AST to a file
    ast
  end
end", dir.to_str().unwrap(), out_file);

    let source = "./src";
    let lib = format!("{}/lib", source);
    let extractor = &*format!("{}/ast_extactor.ex", lib);
    
    std::fs::create_dir(lib.clone())
        .expect("Failed to create lib directory at source");
    
    let ast_extractor = File::create(extractor);

    ast_extractor
        .expect("Failed to create AST extractor")
        .write_all(ast_extractor_code.as_bytes())
        .expect("Failed to write to AST extractor");

    let output = Command::new("mix")
        .args(["run", "-e", "AstExtractor.main"])
        .current_dir(source)
        .output()
        .expect("Failed to execute Elixir script");

    if output.status.success() {
        let mut file = File::open(out_file).expect("Failed to open output file");
        let mut contents = String::new();
        file.read_to_string(&mut contents).expect("Failed to read output file");
        if !silent {
            println!("{}", contents);
        }
    } else {
        println!("Error: {:?}", output.stderr);
    }
    let _ = std::fs::remove_file(extractor);
    let _ = std::fs::remove_dir(lib);
}

fn init_logger(silent: bool) {
    let level = if silent {
        LevelFilter::Off
    } else {
        LevelFilter::Debug
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
        .filter_level(level)
        .init();

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
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block_statements => {
                parse_block_statements(pair, file_writer, ret, func_def);
            },
            _ => parse_warn!("block", pair.as_rule()),
        }
    }
}


pub fn parse_block_statements(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter, ret: bool, func_def: bool) {
    let mut inner_iter = ast_node.into_inner().peekable();
    while let Some(pair) = inner_iter.next() {
        let last = inner_iter.peek().is_none();
        match pair.as_rule() {
            Rule::block_statement => parse_block_statement(pair, file_writer, (last && func_def) || ret, func_def),
            _                     => parse_warn!("block statements", pair.as_rule()),
        }
    }
}

pub fn parse_block_statement(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
    func_def: bool,
) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::function_definition  => parse_function_definition(pair, file_writer, ret),
            Rule::defmodule            => parse_defmodule(pair, file_writer),
            Rule::tuple                => parse_tuple(pair, file_writer, ret, func_def),
            Rule::assignment           => parse_assignment(pair, file_writer, ret, func_def),
            Rule::array_assignment     => parse_array_assignment(pair, file_writer, ret, func_def),
            Rule::array_read           => parse_array_read(pair, file_writer, ret, func_def),
            Rule::send                 => parse_send(pair, file_writer, ret),
            Rule::receive              => parse_receive(pair, file_writer, ret, func_def),
            Rule::io                   => parse_io(pair, file_writer, ret),
            Rule::spawn_process        => parse_spawn_process(pair, file_writer, ret),
            Rule::assigned_variable    => parse_assigned_variable(pair, file_writer, ret),
            Rule::r#for                => parse_for(pair, file_writer, ret, func_def),
            _                          => parse_warn!("block statement", pair.as_rule()),
        }
    }
}

fn parse_assigned_variable(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool
) {
    let variable_name = get_variable_name(ast_node);
    file_writer.write_assigned_variable(&variable_name, ret);
}

fn parse_io(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    _ret: bool
) {
    // Get the block_statement, and print it's string representation
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block_statement => file_writer.write_io(&io_to_str(pair)),
            _ => parse_warn!("io", pair.as_rule()),
        }
    }
}

fn io_to_str(ast_node: Pair<Rule>) -> String {
    let mut out = String::new();
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::string => out.push_str(&pair.as_str().replace('\"', "")),
            Rule::assigned_variable => out.push_str(&get_variable_name(pair)),
            _ => (),
        }
    }
    out
}

fn parse_receive(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
    func_def: bool,
) {
    // Find the receive_statement node and panic if does not exist
    let receive_statement = ast_node
        .clone()
        .into_inner()
        .find(|x| x.as_rule() == Rule::receive_statements)
        .expect("No receive_statements in receive expression");

    let line_number = get_line_number(ast_node.clone());
    file_writer.write_receive(line_number);

    // Parse receive statements
    let mut mtypes = Vec::new();
    for pair in receive_statement.into_inner() {
        match pair.as_rule() {
            Rule::receive_statement => {
                let mtype = parse_receive_statement(pair, file_writer, ret, func_def);
                mtypes.push(mtype);
            },
            _ => parse_warn!("receive", pair.as_rule()),
        }
    }
    file_writer.commit_receive();
}

fn parse_receive_statement(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
    func_def: bool,
) -> String {

    // Preserve order and type
    for pair in ast_node.clone().into_inner() {
        match pair.as_rule() {
            Rule::receive_atom      => parse_receive_atom(pair, file_writer, ret),
            Rule::single_assignment => parse_receive_single(pair, file_writer, ret),
            Rule::pair_assignment   => parse_receive_pair(pair, file_writer, ret),
            Rule::multi_assignment  => parse_receive_multi(pair, file_writer, ret),
            _ => "".to_string(),
        };
    };

    for pair in ast_node.clone().into_inner() {
        match pair.as_rule() {
            Rule::block_statement => parse_block_statement(pair, file_writer, ret, func_def),
            Rule::block           => parse_block(pair, file_writer, ret, func_def),
            _                     => (),
        };
    };

    file_writer.write_end_receive_statement();

    // TODO: this may require to be the mtype from parsing receive (single/pair/multi)  
    "".to_string()
}

fn parse_receive_atom(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    _ret: bool
) -> String {
    let line_number = get_line_number(ast_node.clone());
    let mut assignments = Vec::new();
    let mtype = ast_node.into_inner().next().unwrap().as_str().replace(':', "");
    assignments.push(mtype.clone());
    file_writer.write_receive_assignment(assignments, line_number);
    mtype
}

fn parse_receive_single(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    _ret: bool
) -> String {
    let line_number = get_line_number(ast_node.clone());
    // Find the atom node
    if let Some(x) = ast_node.into_inner().find(|y| y.as_rule() == Rule::atom) {
        let mut assignments = Vec::new();
        let mtype = x.as_str().replace(':', "");
        assignments.push(mtype.clone());
        file_writer.write_receive_assignment(assignments, line_number);
        mtype
    } else {
        panic!("No atom in assigned variable");
    }
}

fn parse_receive_pair(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    _ret: bool
) -> String {
    // Pair guaranteed of the form alpha_letters followed by atom or assigned_variable
    let mut assignments = Vec::new();
    let mut metadata = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::alpha_letters => assignments.push(pair.as_str().to_string()),
            Rule::atom          => assignments.push(pair.as_str().to_string().replace(':', "")),
            Rule::assigned_variable => assignments.push(get_variable_name(pair)),
            Rule::metadata => metadata = Some(pair),
            _ => parse_warn!("receive pair", pair.as_rule()),
        }
    }
    let line_number = get_line_number_from_metadata(metadata);
    if assignments.is_empty() {
        panic!("No assignments in receive pair");
    } else {
        file_writer.write_receive_assignment(assignments.clone(), line_number);
        assignments[0].as_str().to_string() 
    }
}

fn parse_receive_multi(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    _ret: bool
) -> String {
    // Extract all instances of recv_binding to a vector
    let mut assignments = Vec::new();
    let mut metadata = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::recv_binding => {
                assignments.push(get_variable_name(pair));
            },
            Rule::metadata => metadata = Some(pair),
            _ => parse_warn!("receive multi", pair.as_rule()),
        }
    }
    let line_number = get_line_number_from_metadata(metadata);

    // File writing for receive multi
    file_writer.write_receive_assignment(assignments.clone(), line_number);
    if assignments.is_empty() {
        panic!("No assignments in receive multi");
    } else {
        assignments[0].as_str().to_string() 
    }
}

fn parse_send(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    _ret: bool
) {
    let mut send_target = None;
    let mut send_arguments = None;
    let mut send_tupled_arguments = None;
    let mut send_atom = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::send_target           => send_target = Some(pair),
            Rule::send_arguments        => send_arguments = Some(pair),
            Rule::send_tupled_arguments => send_tupled_arguments = Some(pair),
            Rule::send_atom             => send_atom = Some(pair),
            _                           => parse_warn!("send", pair.as_rule()),
        }
    }

    // Create a vector of tuples of argument types and identifiers
    let send_args = extract_send_arguments(send_arguments, send_tupled_arguments, send_atom);

    // Write the send to the file
    if let Some(x) = send_target {
        let var = get_variable_name(x);
        file_writer.write_send(&var, send_args);
    } else {
        panic!("No send target in send expression");
    }
}

/* Takes an operation and produces a string representation that can be evalutated in the frontend */
fn operation_as_string(ast_node: Pair<Rule>) -> String {
    let mut repr = String::new();
    if ast_node.as_rule() == Rule::binary_operation {
        /* Recursive case */
        let mut op = "";
        let mut args = Vec::new(); 
        for pair in ast_node.into_inner() {
            match pair.as_rule() {
                Rule::binary_operator => op = pair.as_str(),
                Rule::binary_operand    => args.push(pair),
                _              => (),
            }
        }
        let str1 = operation_as_string(args[0].to_owned());
        let str2 = operation_as_string(args[1].to_owned());
        repr = format!("{} {} {}", str1, op, str2);
    } else if ast_node.as_rule() == Rule::expression_tuple {
        /* Base case */
        for pair in ast_node.into_inner() {
            if pair.as_rule() == Rule::atom {
                repr = pair.as_str().replace(':', "");
            }
        }
    } else if ast_node.as_rule() == Rule::assigned_variable {
        /* Base case */
        repr = get_variable_name(ast_node);
    } else if ast_node.as_rule() == Rule::string || ast_node.as_rule() == Rule::number {
        repr = ast_node.as_str().to_string();
    } else if ast_node.as_rule() == Rule::binary_operand {
        if let Some(pair) = ast_node.into_inner().next() {
            return match pair.as_rule() {
                Rule::binary_operation  => operation_as_string(pair),
                Rule::expression_tuple  => operation_as_string(pair),
                Rule::binary_operand    => operation_as_string(pair),
                Rule::assigned_variable => operation_as_string(pair),
                Rule::number            => operation_as_string(pair),
                Rule::string            => operation_as_string(pair),
                _                       => panic!("Unexpected type in binary operation string repr"),
            }
        }
    } else {
        panic!("Unhandled string representation of expression type");
    }
    repr
}

fn extract_send_arguments<'a>(send_arguments: Option<Pair<'a, Rule>>, send_tupled_arguments: Option<Pair<'a, Rule>>, send_atom: Option<Pair<'a, Rule>>) -> Vec<String> {
    let mut send_args = Vec::new();
    if let Some(x) = send_arguments {
        for pair in x.into_inner() {
            if pair.as_rule() == Rule::binary_operation {
                send_args.push(operation_as_string(pair));
            } else if pair.as_rule() == Rule::assigned_variable {
                send_args.push(get_variable_name(pair));
            } else if pair.as_rule() != Rule::metadata {
                send_args.push(pair.as_str().to_string());
            }
        }
    } else if let Some(x) = send_tupled_arguments {
        for pair in x.into_inner() {
            if pair.as_rule() == Rule::binary_operation {
                send_args.push(operation_as_string(pair));
            } else if pair.as_rule() == Rule::assigned_variable {
                send_args.push(get_variable_name(pair));
            } else if pair.as_rule() != Rule::metadata {
                send_args.push(pair.as_str().to_string());
            }
        }
    } else if let Some(x) = send_atom { 
        send_args.push(x.as_str().to_string());
    }
    send_args
}

fn get_variable_name(ast_node: Pair<Rule>) -> String {
    if ast_node.as_rule() != Rule::assigned_variable && 
        ast_node.as_rule() != Rule::send_target &&
        ast_node.as_rule() != Rule::recv_binding {
        panic!("Can't get variable name unless type assigned_variable");
    }
    if let Some(x) = ast_node.clone().into_inner().find(|y| y.as_rule() == Rule::atom) {
        return x.as_str().replace(':', "");
    } else if let Some(x) = ast_node.clone().into_inner().find(|y| y.as_rule() == Rule::assigned_variable) {
        return get_variable_name(x);
    } else {
        panic!("Unexpected type in assigned variable");
    }
}

fn parse_assignment(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter, ret: bool, func_def: bool) {
    let mut assigned_variable = None;
    let mut expression = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::assigned_variable   => assigned_variable = Some(pair),
            Rule::expression_argument => expression = Some(pair),
            _                         => (),
        }
    }
    let typ;
    if let Some(x) = expression.clone() {
        typ = get_exp_type(x);
    } else {
        panic!("No expression in assignment expression");
    }
    if let Some(x) = assigned_variable {
        let variable_name = get_variable_name(x);
        file_writer.write_assignment_variable(&variable_name, typ);
    } else {
        panic!("No variable name in assignment expression");
    }
    if let Some(x) = expression {
        parse_expression_tuple(x, file_writer, ret, func_def);
    } else {
        panic!("No expression in assignment expression");
    }
}

fn parse_array_assignment(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    _ret: bool,
    _func_def: bool,
) {
    let mut assigned_variable = None;
    let mut array = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::assigned_variable => assigned_variable = Some(pair),
            Rule::array             => array = Some(pair),
            _                       => (),
        }
    }
    // Get the array type
    let typ;
    if let Some(x) = array.clone() {
        typ = get_array_type(x);
    } else {
        panic!("No array in array assignment expression");
    }
    let variable_name;
    if let Some(x) = assigned_variable {
        variable_name = get_variable_name(x);
        // TODO type the array
        file_writer.write_array_assignment(&variable_name, typ);
    } else {
        panic!("No variable name in array assignment expression");
    }
    if let Some(x) = array {
        let arr_type = x.clone().into_inner().next().unwrap();
        if arr_type.clone().as_rule() == Rule::enum_map_call {
            parse_enum_map(arr_type, file_writer, variable_name);
        } else {
            parse_array(x.clone(), file_writer, false);
        }
    }
}

fn parse_array_read(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    _ret: bool,
    _func_def: bool,
) {
    let mut array_assigned_variable = None;
    let mut expression_argument = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::array_assigned_variable => array_assigned_variable = Some(pair),
            Rule::expression_argument     => expression_argument = Some(pair),
            _                             => (),
        }
    };
    let mut vars = Vec::new();
    if let Some(x) = array_assigned_variable {
        for var in x.into_inner() {
            let var_name = get_variable_name(var);
            if var_name.as_str() != "_" {
                vars.push(var_name);
            }
        }
    } else {
        panic!("No variable name in array read expression");
    };
    if let Some(x) = expression_argument {
        let arg = x.into_inner().next().unwrap();
        let mut assignment = String::new();
        match arg.as_rule() {
            Rule::assigned_variable => assignment = get_variable_name(arg),
            Rule::array => todo!(),
            _           => error!("Unexpected type in array read expression"),
        }
        file_writer.write_array_read(vars, assignment);
    } else {
        panic!("No array in array read expression");
    };
}

// Gets the type of an expression
fn get_exp_type(var: Pair<Rule>) -> sym_table::SymbolType {
    let exp = var.into_inner().next().unwrap();
    match exp.as_rule() {
        Rule::number => sym_table::SymbolType::Integer,
        Rule::negative_number => sym_table::SymbolType::Integer,
        Rule::bool   => sym_table::SymbolType::Boolean,
        Rule::self_pid => sym_table::SymbolType::Integer,
        Rule::string => sym_table::SymbolType::String,
        Rule::spawn_process => sym_table::SymbolType::Integer,
        Rule::array => get_array_type(exp),
        Rule::assigned_variable => sym_table::SymbolType::Unknown,
        Rule::binary_operation => sym_table::SymbolType::Integer,
        _            => {
            parse_warn!("get exp type", exp.as_rule());
            sym_table::SymbolType::Unknown
        },
    }
}

fn get_array_type(array: Pair<Rule>) -> sym_table::SymbolType {
    let mut typ = sym_table::SymbolType::Array(Box::new(sym_table::SymbolType::Unknown), 0);
    for pair in array.into_inner() {
        match pair.as_rule() {
            Rule::primitive_array => {
                let arg = pair.into_inner().next().unwrap();
                match arg.as_rule() {
                    Rule::assigned_variable => typ = sym_table::SymbolType::Array(Box::new(sym_table::SymbolType::Unknown), 0),
                    Rule::primitive => {
                        let primitive = arg.into_inner().next().unwrap();
                        match primitive.as_rule() {
                            Rule::number => typ = sym_table::SymbolType::Array(Box::new(sym_table::SymbolType::Integer), 0),
                            Rule::string => typ = sym_table::SymbolType::Array(Box::new(sym_table::SymbolType::String), 0),
                            Rule::bool   => typ = sym_table::SymbolType::Array(Box::new(sym_table::SymbolType::Boolean), 0),
                            _            => parse_warn!("get array type", primitive.as_rule()),
                        
                        };
                    },
                    _ => (),
                }
            },
            Rule::metadata => (),
            _ => parse_warn!("get array type", pair.as_rule()),
        }
    }
    typ
}

fn get_function_name(ast_node: Pair<Rule>, str_out: &mut String) {
    // TODO return the function name from the node
    str_out.push_str(ast_node.as_str());
    str_out.remove(0);
}

fn get_primitive_as_str(primitive: Pair<Rule>) -> String {
    let rule = primitive.into_inner().next().unwrap();
    match rule.as_rule() {
        Rule::string => format!("\"{}\"", rule.as_str()),
        Rule::self_pid => String::from("__pid"), // TODO this exposes implementation of file_writer
        _            => rule.as_str().to_string(),
    }
}

fn argument_list_as_str(argument_list: Pair<Rule>) -> String {
    let mut out = String::from("");
    for argument in argument_list.into_inner() {
        for arg_type in argument.into_inner() {
            match arg_type.as_rule() {
                Rule::primitive => {
                    out += get_primitive_as_str(arg_type).as_str();
                },
                Rule::assigned_variable => {
                    let x: String = get_variable_name(arg_type);
                    out += x.as_str();
                },
                _ => parse_warn!("argument list as str", arg_type.as_rule()),
            }
        }
        out.push(',');
    }
    if !out.is_empty() {
        out.pop();
    }
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
        for (i, pair) in x.into_inner().enumerate() {
            sym_table.add_entry(args_v.get(i).expect("arguments and types size misalign").to_string(), get_symbol_type(pair));
        }
    } else {
        panic!("no argument types");
    }

    sym_table
}

pub fn parse_function_definition(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    _ret: bool,
) {
    // Write a new function name to the output file
    let mut func_name = String::new();
    // [function_name, metadata, arguments, do]
    let mut func_name_node: Option<Pair<Rule>> = None;
    let mut func_body_node: Option<Pair<Rule>> = None;
    let mut func_arg_node: Option<Pair<Rule>> = None;
    let mut func_type_spec: Option<Pair<Rule>> = None;
    let mut vae_init = false;
    let mut ltl_spec: Option<Pair<Rule>> = None;
    let mut _func_metadata_node: Option<Pair<Rule>> = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::function_name      => func_name_node = Some(pair), 
            Rule::function_arguments => func_arg_node = Some(pair),
            Rule::r#do               => func_body_node = Some(pair),
            Rule::metadata           => _func_metadata_node = Some(pair),
            Rule::type_spec          => func_type_spec = Some(pair),
            Rule::vae_init           => vae_init = true,
            Rule::ltl_spec           => ltl_spec = Some(pair),
            _                        => parse_warn!("function definition", pair.as_rule()),
        }
    }
    
    get_function_name(func_name_node.unwrap(), &mut func_name);
    let args = &*argument_list_as_str(func_arg_node.expect("no function arguments"));
    let sym_table;
    let mut arg_var_intersect = Vec::new();
    if let Some(x) = ltl_spec {
        // ltl spec will be last element
        let ltl = x.into_inner().next_back().unwrap();
        let ltl_vars = get_vars_from_ltl(ltl.clone());
        // The intersection between the ltl vars and the args will be instrumented
        arg_var_intersect = collect_common_elements(args, ltl_vars);
        file_writer.write_ltl(ltl.as_str());
    }

    if let Some(x) = func_type_spec {
        sym_table = create_function_symbol_table(args, x);
    } else {
        sym_table = internal_representation::sym_table::SymbolTable::new();
        error!("Missing type spec for function {}.", func_name);
    }
    file_writer.new_function(&func_name, args, sym_table, vae_init, arg_var_intersect);
    
    // Write the body 
    // Start by setting up the channels
    // Use predefiend code blocks for send and recv
    parse_do(func_body_node.unwrap(), file_writer, false, !vae_init);

    // Close the function 
    file_writer.commit_function();
    // file_writer.commit().expect("Failed to commit to file");
}

fn collect_common_elements<'a>(args: &'a str, ltl_vars: Vec<String>) -> Vec<String> {
    // Helper function for collecting intersection of args and ltl vars
    let mut common = Vec::new();
    let args_v: Vec<&str> = args.split(',').map(|s| s.trim()).collect();
    for arg in args_v {
        let arg_s = arg.to_string();
        if ltl_vars.contains(&arg_s) {
            common.push(arg_s);
        }
    }
    common
}

fn get_vars_from_ltl(ltl: Pair<Rule>) -> Vec<String> {
    // Recursively descend the ltl tree and extract all variables
    let mut vars = Vec::new();
    for pair in ltl.into_inner() {
        match pair.as_rule() {
            Rule::alpha_letters => { // Base case
                vars.push(pair.as_str().to_string());
            },
            Rule::ltl_primitive => { // Recursive cases
                vars.append(&mut get_vars_from_ltl(pair));
            },
            Rule::ltl_term => {
                vars.append(&mut get_vars_from_ltl(pair));
            },
            Rule::ltl_opd => {
                vars.append(&mut get_vars_from_ltl(pair));
            },
            Rule::ltl_unary_term => {
                vars.append(&mut get_vars_from_ltl(pair));
            },
            Rule::ltl => {
                vars.append(&mut get_vars_from_ltl(pair));
            }
            _ => (),
        }
    }
    vars.sort();
    vars.dedup();
    vars
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
            Rule::tuple           => parse_tuple(pair, file_writer, ret || func_def, func_def),
            Rule::block_statement => parse_block_statement(pair, file_writer, ret || func_def, func_def),
            _                     => parse_warn!("do single", pair.as_rule()), 
           }
    }
}

fn parse_tuple(    
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
    func_def: bool,
) {
    // Given a tuple does not begin with an identified keyword i.e.
    // is an "atom", we assume it is a function call
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::expression_tuple    => parse_expression_tuple(pair, file_writer, ret, func_def),  
            Rule::binary_operation    => parse_binary_operation(pair, file_writer, ret),
            Rule::r#if                => parse_if(pair, file_writer, ret, func_def),
            Rule::unless              => parse_unless(pair, file_writer, ret, func_def),
            Rule::function_definition => parse_function_definition(pair, file_writer, ret),
            Rule::metadata            => (),
            Rule::io                  => parse_io(pair, file_writer, ret),
            Rule::receive             => parse_receive(pair, file_writer, ret, func_def),
            // TODO this case doesn't make sense, error in parsing somewhere
            Rule::tuple               => parse_tuple(pair, file_writer, ret, func_def),
            _                         => parse_warn!("tuple", pair.as_rule()),
        }
    }
}

/// Converts a tuple argument into a string representation
/// For now, only support negative numbers
/// TODO: support all expression types and do blocks
fn resolve_tuple_argument(ast_node: Pair<Rule>) -> &str {
    println!("{}\n{}", ast_node, ast_node.as_str());
    panic!("TODO implement tuple arguments");
}

fn resolve_negative_number(ast_node: Pair<Rule>) -> &str {
    for pair in ast_node.into_inner() {
        if pair.as_rule() == Rule::number {
                let s = format!("-{}", pair.as_str());
                return Box::leak(s.into_boxed_str());
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
            let arg_s: String = match arg.as_rule() {
                Rule::r#number => arg.as_str().to_string(),
                Rule::r#string => arg.as_str().to_string(),
                Rule::negative_number => resolve_negative_number(arg).to_string(),
                Rule::tuple    => resolve_tuple_argument(arg).to_string(),
                Rule::assigned_variable => {
                    let variable_name = get_variable_name(arg);
                    variable_name.to_string()
                },
                Rule::binary_operation => operation_as_string(arg),
                _ => panic!("Failed to find argument in argument list")
            };
            out.push_str(&arg_s);
            out.push(',');
        }
    }
    out.pop();
    out.push(']');
    out
}

fn parse_expression_tuple(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,    
    func_def: bool,
) {
    let mut _io_node: Option<Pair<Rule>> = None;
    let mut atom_node: Option<Pair<Rule>> = None;
    let mut arguments_node: Option<Pair<Rule>> = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::io                   => _io_node = Some(pair), 
            Rule::atom                 => atom_node = Some(pair),
            Rule::expression_arguments => arguments_node = Some(pair),
            Rule::spawn_process        => parse_spawn_process(pair, file_writer, ret),
            Rule::tuple                => {
                parse_tuple(pair, file_writer, ret, func_def)
            },
            Rule::array                => parse_array(pair, file_writer, ret),
            Rule::enum_call            => parse_enum_call(pair, file_writer, ret),
            _                          => parse_warn!("expression tuple", pair.as_rule()),
        }
    }

    if let Some(x) = atom_node {
        let mut func_name = x.as_str().to_string();
        func_name.remove(0);
        if let Some(arguments) = arguments_node {
            let call_args = parse_call_arguments(arguments);
            file_writer.write_function_call(&func_name, &call_args, ret);
        } else {
            file_writer.write_function_call(&func_name, "", ret);
        }
    }

}

fn parse_enum_call(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    _ret: bool
) {
    let mut func = None;
    let mut args = Vec::new();
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::enum_func           => func = Some(pair),
            Rule::expression_argument => args.push(pair),
            _                         => parse_warn!("enum call", pair.as_rule()),
        }
    }
    if let Some(x) = func {
        let func_type = x.into_inner().next().unwrap();
        match func_type.as_rule() {
            Rule::enum_random => {
                // single arg, of type assigned variable
                let mut string_args = Vec::new();
                for arg in args {
                    let arg_type = arg.into_inner().next().unwrap();
                    match arg_type.as_rule() {
                        Rule::assigned_variable => string_args.push(get_variable_name(arg_type)),
                        _                       => error!("Enum random calls only support usage on variables"),
                    }
                }
                if string_args.len() != 1 {
                    error!("Enum random calls only support one argument (variable)");
                }
                file_writer.write_enum_random(string_args);
            },
            Rule::enum_at => {
                // two args, an assigned variable and a number
                let mut string_args = Vec::new();
                for arg in args {
                    let arg_type = arg.into_inner().next().unwrap();
                    match arg_type.as_rule() {
                        Rule::assigned_variable => string_args.push(get_variable_name(arg_type)),
                        Rule::number            => string_args.push(arg_type.as_str().to_string()),
                        _                       => error!("Enum at calls only support usage on variables and numbers"),
                    }
                }
                if string_args.len() != 2 {
                    error!("Enum at calls only support two arguments (variable, number)");
                }
                file_writer.write_enum_at(string_args);
            },
            _ => warn!("Tried writing unsupported enum function"),
        }
    } else {
        panic!("No function name in enum call");
    }
}

fn parse_enum_map(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    assignee: String,
) {
    let mut args = Vec::new();
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::expression_argument => args.push(pair),
            _                         => parse_warn!("enum call", pair.as_rule()),
        }
    }
    // two args, an assigned variable and an anonymous function
    let mut iterable = None;
    let mut func = None;
    for arg in args {
        if arg.as_rule() == Rule::expression_argument {
            let arg_type = arg.into_inner().next().unwrap();
            match arg_type.as_rule() {
                Rule::assigned_variable  => iterable = Some(get_variable_name(arg_type)),
                Rule::anonymous_function => func = Some(arg_type),
                _                        => error!("Enum map call only supports variables and anonymous functions"),
            }
        }
    }
    if let Some(x) = iterable {
        if let Some(y) = func {
            let mut fn_args = Vec::new();
            let mut fn_body = None;
            for pair in y.into_inner() {
                match pair.as_rule() {
                    Rule::assigned_variable => fn_args.push(get_variable_name(pair)),
                    Rule::block_statement   => fn_body = Some(pair),
                    _                       => (),
                }
            }

            file_writer.write_enum_map(x, fn_args, assignee);
            if let Some(z) = fn_body {
                // Return is true as writing anonymous function
                parse_block_statement(z, file_writer, true, false);
            } else {
                panic!("No function body in enum map call");
            }
            file_writer.commit_enum_map();
        } else {
            error!("Enum map call missing function argument");
        }
    } else {
        error!("Enum map call missing variable argument");
    }
}

fn parse_spawn_process(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    _ret: bool
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
            file_writer.write_spawn_process(&x.as_str().replace(':', ""), args);
        } else {
            panic!("No process type provided in spawn");
        }        
    } else {
        panic!("No process type provided in spawn");
    }
}

fn parse_array(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    _ret: bool
) {
    // Array is either primitive_array or cons
    let mut elements = Vec::new(); 
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::primitive_array => {
                pair.into_inner().for_each(|x| elements.push(x.as_str().to_string()));
            },
            Rule::function_argument => {
                let arg = pair.into_inner().next().unwrap();
                match arg.as_rule() {
                    Rule::assigned_variable => elements.push(get_variable_name(arg)),
                    Rule::primitive         => elements.push(get_primitive_as_str(arg)),
                    _                       => error!("Unexpected function argument in non-primitive array"),
                }
            },
            Rule::binary_operand => {
                let arg = pair.into_inner().next().unwrap();
                match arg.as_rule() {
                    Rule::binary_operation  => elements.push(operation_as_string(arg)),
                    Rule::assigned_variable => elements.push(get_variable_name(arg)),
                    Rule::number         => elements.push(arg.as_str().to_string()),
                    Rule::string         => elements.push(arg.as_str().to_string()),
                    Rule::primitive_array => {
                        let arr_elements = get_elements_from_primitive_array(arg);
                        for element in arr_elements {
                            elements.push(element);
                        }
                    },
                    _                       => error!("Unexpected binary operand in non-primitive array"),
                }
            },
            _                     => parse_warn!("array", pair.as_rule()),
        }
    }
    file_writer.write_array(elements);
}

fn get_elements_from_primitive_array(
    ast_node: Pair<Rule>
) -> Vec<String> {
    let mut elements = Vec::new();
    for pair in ast_node.into_inner() {
        let arg = pair.clone().into_inner().next().unwrap();
        match arg.as_rule() {
            Rule::primitive => elements.push(get_primitive_as_str(pair)),
            Rule::assigned_variable => elements.push(get_variable_name(pair)),
            _               => parse_warn!("get elements from primitive array", pair.as_rule()),
        }
    }
    elements
}

fn parse_unless(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
    func_def: bool,
) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::conditions => parse_unless_conditions(pair, file_writer, ret, func_def),
            _                => parse_warn!("unless", pair.as_rule()),
        }
    }
}

fn parse_if(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
    func_def: bool,
) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::conditions => parse_conditions(pair, file_writer, ret, func_def),
            _                => parse_warn!("if", pair.as_rule()),
        }
    }
}

fn create_condition(
    ast_node: Pair<Rule>
) -> internal_representation::formatted_condition::FormattedCondition {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::primitive => {
                // Check if primitive is bool
                let cond = pair.into_inner().next().unwrap();
                match cond.as_rule() {
                    Rule::bool   => return internal_representation::formatted_condition::FormattedCondition::Boolean(cond.as_str().parse().unwrap()),
                    Rule::number => return internal_representation::formatted_condition::FormattedCondition::Number(cond.as_str().parse().unwrap()),
                    _            => return internal_representation::formatted_condition::FormattedCondition::Primitive(cond.as_str().to_string()),       
                }
            },
            Rule::assigned_variable => return internal_representation::formatted_condition::FormattedCondition::Variable(get_variable_name(pair)),
            Rule::or => {
                let mut operands = Vec::new();
                for cond in pair.into_inner() {
                    if let Rule::boolean_operand = cond.as_rule() {
                        operands.push(create_condition(cond))
                    }
                }
                
                if operands.len() < 2 {
                    panic!("Not enough operands for 'or' operation");
                }
            
                // Take ownership of the operands
                let l_op = operands.remove(0);
                let r_op = operands.remove(0);
            
                // Return new FormattedCondition
                return internal_representation::formatted_condition::FormattedCondition::BinaryOperation("or", Box::new(l_op), Box::new(r_op));
            },            
            Rule::and => {
                let mut operands = Vec::new(); 
                for cond in pair.into_inner() {
                    if let Rule::boolean_operand = cond.as_rule() {
                        operands.push(create_condition(cond))
                    }
                }

                if operands.len() < 2 {
                    panic!("Not enough operands for 'or' operation");
                }
            
                // Take ownership of the operands
                let l_op = operands.remove(0);
                let r_op = operands.remove(0);
 
                // Return new FormattedCondition
                return internal_representation::formatted_condition::FormattedCondition::BinaryOperation("and", Box::new(l_op), Box::new(r_op));
            },
            Rule::not => {
                // Recurse into the condition
                let Some(condition) = pair.clone().into_inner().find(|a| a.as_rule() == Rule::boolean_operand) else { todo!() };
                let expr = create_condition(condition);

                // Return new FormattedCondition
                return internal_representation::formatted_condition::FormattedCondition::Not(Box::new(expr));
            },
            Rule::boolean_operation => {
                // Operation
                let Some(operator) = pair.clone().into_inner().find(|a| a.as_rule() == Rule::boolean_operator) else { todo!() };
                
                // Recursve into operands
                let mut operands = Vec::new(); 
                for cond in pair.into_inner() {
                    if let Rule::boolean_operand = cond.as_rule() {
                        operands.push(create_condition(cond))
                    }
                }

                if operands.len() < 2 {
                    panic!("Not enough operands for 'or' operation");
                }
            
                // Take ownership of the operands
                let l_op = operands.remove(0);
                let r_op = operands.remove(0);
 
                // Return new FormattedCondition
                return internal_representation::formatted_condition::FormattedCondition::BinaryOperation(operator.as_str(), Box::new(l_op), Box::new(r_op));
            },
            Rule::boolean_operand => {
                return create_condition(pair);
            },
            _ => panic!("Failed to create condition from node")
        }
    }
    
    internal_representation::formatted_condition::FormattedCondition::Number(1)
} 

fn parse_conditions(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
    func_def: bool,
) {
    // TODO write the translation for conditions
    let mut do_block: Option<Pair<Rule>> = None;
    let mut do_else_block: Option<Pair<Rule>> = None;
    let mut condition: Option<Pair<Rule>> = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::boolean_operand      => condition = Some(pair), 
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
        parse_do(x, file_writer, ret, func_def);
        file_writer.commit_if();
        return;
    }
    
    // If required, write the else
    let do_else_block = do_else_block       
        .unwrap_or_else(|| panic!("No do or do else in if"));

    let mut do_else_block = do_else_block.into_inner();
    if let Some(pair) = do_else_block.next() {
        match pair.as_rule() {
            Rule::primitive       => parse_primitive(pair, file_writer, ret),
            Rule::block_statement => parse_block_statement(pair, file_writer, ret, func_def),
            Rule::block           => parse_block(pair, file_writer, ret, func_def),
            _                     => parse_warn!("conditions", pair.as_rule()),
        }            
    }
    file_writer.write_else();
    
    if let Some(pair) = do_else_block.next() {
        match pair.as_rule() {
            Rule::block_statement => parse_tuple(pair, file_writer, ret, func_def),
            Rule::primitive       => parse_primitive(pair, file_writer, ret),
            _                     => parse_warn!("conditions", pair.as_rule()),
        }
    }
    file_writer.commit_if();
}

fn parse_unless_conditions(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    ret: bool,
    func_def: bool,
) {
    let mut do_block: Option<Pair<Rule>> = None;
    let mut _do_else_block: Option<Pair<Rule>> = None;
    let mut condition: Option<Pair<Rule>> = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::boolean_operand      => condition = Some(pair), 
            Rule::r#do                 => do_block = Some(pair),
            Rule::do_else              => _do_else_block = Some(pair),
            _                          => parse_warn!("conditions", pair.as_rule()),
        }
    }

    file_writer.start_unless();

    let condition = condition
        .unwrap_or_else(|| panic!("Unconditional if"));
    
    // Parse the do block
    if let Some(x) = do_block {
        parse_do(x, file_writer, ret, func_def);
    }
    
    // Write the unless statement
    let formatted_condition = create_condition(condition);
    file_writer.write_unless_condition(formatted_condition);
}


fn parse_primitive(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, ret: bool
) {
    file_writer.write_primitive(ast_node.as_str(), ret);
}

fn name_from_tuple_str(input: &str) -> &str {
    // Check if the input string starts with "{:" and ends with "}"
    if input.starts_with("{:") && input.ends_with('}') {
        // Remove leading "{:" and trailing "}"
        let content = &input[2..(input.len() - 1)];

        // Split the content into parts separated by commas
        let parts: Vec<&str> = content.split(',').map(|s| s.trim()).collect();

        // Check if there are at least two parts (name and other content)
        if parts.len() >= 2 {
            // Extract and return the name (the first part)
            return parts[0];
        }
    }

    // If not a tuple, likely already primitive
    input
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
            Rule::binary_operand => operands.push(pair), 
            _ => (),
        }
    }

    // TODO order the binary operation
    // TODO recursive function call to evaluate expression such as 1 + 1 + 1
    // i.e. {} {} {} operands[0], operator, operands[1]
    if let Some(x) = binary_operator {
        let operand_left = name_from_tuple_str(operands[0].as_str());
        let operand_right = name_from_tuple_str(operands[1].as_str());
        file_writer.write_operation(x.as_str(), operand_left, operand_right, ret);
    }
}

fn parse_for(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, 
    _ret: bool,
    _func_def: bool,
) {
    let mut iterator = None;
    let mut do_block = None;
    let mut iterable = None;
    let mut iterable_as_array = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::assigned_variable => {
                if iterator.is_none() {
                    iterator = Some(pair);
                } else {
                    iterable = Some(pair);
                }
            },
            Rule::r#do   => do_block = Some(pair),
            Rule::array  => iterable_as_array = Some(pair),
            _            => parse_warn!("for", pair.as_rule()),
        }
    }

    if let Some(x) = iterator {
        if let Some(y) = iterable {
            let iterator_name = get_variable_name(x);
            let iterable_name = get_variable_name(y);
            file_writer.write_basic_for_loop(&iterator_name, &iterable_name);
            if let Some(z) = do_block {
                parse_do(z, file_writer, false, false);
            }
            file_writer.commit_for_loop();
        } else if let Some(_y) = iterable_as_array {
            todo!()
        } else {
            panic!("No iterable in for loop");
        }
    } else {
        panic!("No iterator in for loop");
    }
    
}

fn get_line_number_from_metadata(metadata: Option<Pair<Rule>>) -> u32 {
    if let Some(x) = metadata {
        let re = Regex::new(r"line: (\d+)").expect("Failed to compile regex");
    
        if let Some(captures) = re.captures(x.as_str()) {
            let line_number = captures[1].parse();
            if let Ok(y) = line_number {
                return y;
            }
        }
    }
    0
}

fn get_line_number(ast_node: Pair<Rule>) -> u32 {
    let mut metadata = None;
    for pair in ast_node.into_inner() {
        if pair.as_rule() == Rule::metadata { metadata = Some(pair) }
    }
    get_line_number_from_metadata(metadata)
}