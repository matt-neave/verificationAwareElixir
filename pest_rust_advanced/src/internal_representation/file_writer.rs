use std::fs::File;
use std::collections::HashMap;
use std::io::{self, Write};

use crate::formatted_condition;
use crate::internal_representation::sym_table;

pub struct FileWriter {
    content: String,
    function_body: String,
    function_metabody: String,
    function_call_count: u32,
    file: File,
}

impl FileWriter {
    // Constructor method to create a new instance
    pub fn new(file_path: &str) -> io::Result<Self> {
        let file = File::create(file_path)?;
        Ok(Self {
            content: String::new(),
            function_body: String::new(),
            function_metabody: String::new(),
            function_call_count: 0,
            file,
        })
    }

    // Method to append text to the string
    pub fn write(&mut self, text: &str) {
        self.content.push_str(text);
    }

    // Method to append text to the string with new line
    pub fn writeln(&mut self, text: &str) {
        self.function_body.push_str(format!("{}\n", text).as_str());
    }

    pub fn write_operation(&mut self, operand: &str, left_e: &str, right_e: &str, ret: bool) {
        let formatted_string = if ret {
            format!("ret ! {} {} {}\n", left_e, operand, right_e)
        } else {
            format!("{} {} {}\n", left_e, operand, right_e)
        };
        self.function_body.push_str(formatted_string.as_str());
    }
    
    fn type_to_str(t: &sym_table::SymbolType) -> String {
        match t {
            sym_table::SymbolType::Integer => String::from("int"),
            sym_table::SymbolType::String => String::from("byte"),
            sym_table::SymbolType::Boolean => String::from("int"),
            _ => String::new()
        }
    }

    fn format_arguments(arguments: &str, sym_table: sym_table::SymbolTable) -> String {
    let mut out = String::new();
    let arg_ls = arguments.split(",");
    for arg in arg_ls {
        let t = sym_table.lookup(arg);
        out += &Self::type_to_str(t);
        out += " ";
        out += arg;
        out += ",";
    }
    out.pop();
    out
}


    pub fn new_function(&mut self, func_name: &str, arguments: &str, sym_table: sym_table::SymbolTable) {
        // TODO: look into using annotation instead of matching on start
        match &*func_name {
            "start" => self.content.push_str(&*format!("init {{\n")),
            _       => 
                if arguments.is_empty() {
                    self.content.push_str(&*format!("proctype {} (chan ret) {{\n", &*func_name));
                } else {
                    let formatted_args = Self::format_arguments(arguments, sym_table);
                    self.content.push_str(&*format!("proctype {} (chan ret, {}) {{\n", &*func_name, &*formatted_args));
                },
        }
    }

    pub fn commit_function(&mut self) {
        // Commits the current function to the file
        self.content.push_str(&*format!("{}", &*self.function_metabody));
        self.content.push_str(&*format!("{}}}\n\n", &*self.function_body));
        self.function_metabody = String::new();
        self.function_body = String::new();
        self.function_call_count = 0;
    }

    pub fn write_function_call(&mut self, func_name: &str, call_arguments: &str, return_variable: &str, _ret: bool /* TODO */) {
        // Track how many function calls have taken place 
        // Create a channel for each
        // Name the receive variables appropriately
        // TODO determine return type    
        self.function_call_count += 1;
        self.function_metabody.push_str(&*format!("chan ret{} = [1] of {{ int }};\n", self.function_call_count));
        
        // TODO make a mapping of variable name
        let call_arguments = call_arguments.replace("[", "(");
        let call_arguments = call_arguments.replace("]", "");
        self.function_body.push_str(&*format!("run {}{}, ret{});\n", func_name, call_arguments, self.function_call_count));
        self.function_body.push_str(&*format!("int {};\n", return_variable));
        self.function_body.push_str(&*format!("ret{} ? {}\n", self.function_call_count, return_variable)); 
    }

    fn condition_to_string(expr: &formatted_condition::FormattedCondition) -> String {
        let mut symbol_map = HashMap::new();
        symbol_map.insert("or", "||");
        symbol_map.insert("and", "&&");    
        match expr {
            formatted_condition::FormattedCondition::Number(n) => n.to_string(),
            formatted_condition::FormattedCondition::Boolean(b) => b.to_string(),
            formatted_condition::FormattedCondition::StringLiteral(s) => format!("\"{}\"", s),
            formatted_condition::FormattedCondition::Primitive(s) => format!("\"{}\"", s),
            formatted_condition::FormattedCondition::BinaryOperation(op, left, right) => {
                format!("({} {} {})", Self::condition_to_string(left), symbol_map.get(op).unwrap_or(&"Missing operator"), Self::condition_to_string(right))
            }
        }
    }

    pub fn write_if_condition(
        &mut self,
        condition: formatted_condition::FormattedCondition
    ) {
        self.function_body.push_str("if\n");
        self.function_body.push_str(format!(":: {} -> \n", Self::condition_to_string(&condition)).as_str());
    }

    pub fn write_else(&mut self) {
        self.function_body.push_str("else ->\n");
    }

    pub fn commit_if(&mut self) {
        self.function_body.push_str("fi\n");
    }

    // Method to commit the content to the file and reset the string
    pub fn commit(&mut self) -> io::Result<()> {
        self.file.write_all(self.content.as_bytes())?;
        self.content.clear(); // Reset the string
        Ok(())
    }

    pub fn write_primitive(&mut self, primitive: &str, ret: bool) {
        let formatted_string = if ret {
            format!("ret ! {}\n", primitive)
        } else {
            format!("{}\n", primitive)
        };
        self.function_body.push_str(&formatted_string);
        
    }
}