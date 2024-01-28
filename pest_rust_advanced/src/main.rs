use std::fs;
use std::env;
use pest::Parser;
use pest_derive::Parser;
use pest::iterators::Pair;

mod internal_representation;
use internal_representation::formatted_condition;

#[derive(Parser)]
#[grammar = "elixir_ast_v1.pest"]
pub struct ASTParser;

fn main() {
    let args: Vec<String> = env::args().collect();
    let default_path = "./simple_ast.txt";

    let path = if args.len() > 1 {
        &args[1]
    } else {
        default_path
    };

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
            Rule::r#do       => parse_do(pair, file_writer, false, false),
            Rule::metadata   => (),
            Rule::alias_name => (),
            _                => println!("undefined1"),
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
            _           => println!("undefined2"),
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
            _ => println!("undefined3"),
        }
    }
}


pub fn parse_block_statements(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter, ret: bool) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::block_statement => parse_block_statement(pair, file_writer, ret),
            _                     => println!("undefined4"),
        }
    }
}

pub fn parse_block_statement(ast_node: Pair<Rule>, file_writer: &mut internal_representation::file_writer::FileWriter, ret: bool) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::function_definition => parse_function_definition(pair, file_writer, ret),
            Rule::tuple               => parse_tuple(pair, file_writer, ret),
            _                         => println!("undefined5"),
        }
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
    let mut _func_metadata_node: Option<Pair<Rule>> = None;
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::function_name      => func_name_node = Some(pair), 
            Rule::function_arguments => func_arg_node = Some(pair),
            Rule::r#do               => func_body_node = Some(pair),
            Rule::metadata           => _func_metadata_node = Some(pair),
            _                        => println!("undefined6"),
        }
    }
    
    get_function_name(func_name_node.unwrap(), &mut func_name);
    file_writer.new_function(&*func_name, &*argument_list_as_str(func_arg_node.expect("no function arguments")));
    

    // Write the body 
    // Start by setting up the channels
    // Use predefiend code blocks for send and recv
    parse_do(func_body_node.unwrap(), file_writer, ret, true);

    // Close the function 
    file_writer.commit_function();
    file_writer.commit().expect("Failed to commit to file");
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
            _               => println!("undefined7"), 
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
            Rule::tuple => parse_tuple(pair, file_writer, ret || func_def),
            _           => println!("undefined8"), 
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
            _                         => println!("undefined9"),
        }
    }
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
            file_writer.write_function_call(&*func_name, &*arguments.as_str(), "val" /* TODO, replace with var name if assignment */, ret);
        } else {
            file_writer.write_function_call(&*func_name, "", "val", ret);
        }
    }

}

fn parse_if(
    ast_node: Pair<Rule>, 
    file_writer: &mut internal_representation::file_writer::FileWriter, ret: bool
) {
    for pair in ast_node.into_inner() {
        match pair.as_rule() {
            Rule::conditions => parse_conditions(pair, file_writer, ret),
            _                => println!("undefined11"),
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
            _               => println!("undefined13"),
        }            
    }
    file_writer.write_else();
    
    if let Some(pair) = do_else_block.next() {
        match pair.as_rule() {
            Rule::tuple     => parse_tuple(pair, file_writer, ret),
            Rule::primitive => parse_primitive(pair, file_writer, ret),
            _               => println!("undefined13"),
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
