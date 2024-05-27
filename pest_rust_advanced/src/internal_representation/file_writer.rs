use std::borrow::Borrow;
use std::ffi::IntoStringError;
use std::fs::File;
use std::collections::HashMap;

use std::io::{self, Write};

use log::{error, warn};
use regex::Regex;

use crate::formatted_condition;
use crate::internal_representation::sym_table::{self};
use crate::internal_representation::boilerplate::add_linked_list_boiler_plate;
use crate::internal_representation::model_generator::PARAM_STR;

use super::sym_table::SymbolType;

// Todo: bodies should be stack based to handle nesting
pub struct FileWriter {
    _header: String,
    content: String,
    function_body: Vec<String>,
    function_channels: Vec<String>,
    function_metabody: Vec<String>,
    function_sym_table: sym_table::SymbolTable,
    ltl_specs: String,
    ltl_header: String,
    ltl_func: bool,
    function_call_count: u32,
    process_count: i32,
    mailbox_id: HashMap<String, i32>,
    process_name: HashMap<i32, String>,
    var_stack: Vec<Vec<String>>,
    var_stack_p: usize,
    mtype: Vec<String>,
    _maximum_message_size: u32,
    function_messages: u32,
    receive_count: u32,
    ltl_count: i32,
    arr_cp_count: u32,
    file: File,
    module: String,
    array_var_stack: Vec<String>,
    anonymous_function_count: u32,
    returning_function: bool,
    ltl_vars: Vec<String>,
    used_ltl_vars: Vec<String>,
    post_condition: String,
    init: bool,
    skip_bounded: bool,
    random_count: u32,
    block_assignment: bool,
    max_process_count: u32,
    parameterized_model: bool,
    parameterized_function: bool,
    parameterized_vars: Vec<String>,
}


impl FileWriter {
    // Constructor method to create a new instance
    pub fn new(file_path: &str, skip_bounded: bool, gen_params: bool) -> io::Result<Self> {
        let file = File::create(file_path)?;
        Ok(Self {
            _header: String::new(),
            content: String::new(),
            function_body: Vec::new(),
            function_channels: Vec::new(),
            function_metabody: Vec::new(),
            function_sym_table: sym_table::SymbolTable::new(),
            ltl_specs: String::new(),
            ltl_header: String::new(),
            ltl_func: false,
            function_call_count: 0,
            process_count: 0,
            mailbox_id: HashMap::new(),
            process_name: HashMap::new(),
            var_stack: Vec::new(),
            var_stack_p: 0,
            mtype: Vec::new(),
            _maximum_message_size: 1,
            function_messages: 0,
            receive_count: 0,
            ltl_count: 0,
            arr_cp_count: 0,
            file,
            module: String::new(),
            array_var_stack: Vec::new(),
            anonymous_function_count: 0,
            returning_function: true,
            ltl_vars: Vec::new(),
            used_ltl_vars: Vec::new(),
            post_condition: String::new(),
            init: false,
            skip_bounded,
            random_count: 0,
            block_assignment: false,
            max_process_count: 10,
            parameterized_model: gen_params,
            parameterized_function: false,
            parameterized_vars: Vec::new(),
        })
    }

    // Method to append text to the string
    pub fn write(&mut self, text: &str) {
        self.content.push_str(text);
    }

    fn post_condition_check(&mut self, line_number: u32) {
        if !self.post_condition.is_empty() {
            self.function_body.last_mut().unwrap().push_str(&format!("assert({}); /*{}*/\n", self.post_condition, line_number));
        }
    }

    // Method to append text to the string with new line
    pub fn writeln(&mut self, text: &str) {
        self.function_body.last_mut().unwrap().push_str(format!("{}\n", text).as_str());
    }

    pub fn write_operation(&mut self, operand: &str, left_e: &str, right_e: &str, ret: bool) {
        let formatted_string = if ret && self.returning_function {
            self.post_condition_check(0);
            format!("ret ! {} {} {};\n", left_e, operand, right_e)
        } else if let Some(x) = self.get_next_var_safe() {
            format!("{} = {} {} {}; \n", x, left_e, operand, right_e)            
        } else {
            format!("{} {} {}", left_e, operand, right_e)
        };
        self.function_body.last_mut().unwrap().push_str(formatted_string.as_str());
    }
    
    fn type_to_str(t: &sym_table::SymbolType) -> String {
        match t {
            sym_table::SymbolType::Integer => String::from("int"),
            sym_table::SymbolType::String => String::from("byte"),
            sym_table::SymbolType::Boolean => String::from("int"),
            sym_table::SymbolType::Atom    => String::from("int"),
            sym_table::SymbolType::NoRet   => String::from("unparsable type"),
            sym_table::SymbolType::Array(x, _) => format!("{}[]", Self::type_to_str(x)),
            sym_table::SymbolType::Unknown => String::from("int"),
        }
    }

    fn format_arguments(arguments: &str, sym_table: &sym_table::SymbolTable) -> String {
    let mut out = String::new();
    let arg_ls = arguments.split(',');
    for arg in arg_ls {
        let t = sym_table.lookup(arg);
        out += &Self::type_to_str(t);
        out += " ";
        out += arg;
        out += ";";
    }
    out.pop();
    out
}


    pub fn new_function(
        &mut self, 
        func_name: &str, 
        arguments: &str, 
        mut sym_table: sym_table::SymbolTable, 
        init: bool, 
        func_arg_ltl_vars: Vec<String>,
        ltl_vars: Vec<String>,
    ) {
        self.function_body.push(String::new());
        self.function_metabody.push(String::new());
        self.function_channels.push(String::new());
        let mut string_args = arguments.to_string();
        // Rename each arg in the ltl_vars with a unique name
        self.ltl_vars = ltl_vars.clone();
        for (i, var) in func_arg_ltl_vars.iter().enumerate() {
            // TODO for now, all ltl vars are INTEGERS
            let ltl_arg = format!("__ltl_{}", i);
            string_args  = string_args.replace(var, &ltl_arg);
            self.ltl_header.push_str(&format!("int {};\n", var));
            sym_table.add_entry(ltl_arg, sym_table::SymbolType::Integer);
            self.function_body.last_mut().unwrap().push_str(&format!("{} = __ltl_{};\n", var, i));
        }
        
        self.returning_function = !matches!(*sym_table.get_return_type(), sym_table::SymbolType::NoRet);
        if init {
            self.init = true;
            // TODO: for now, function name is pushed to the channels as this is the first commit to the file
            self.function_channels.last_mut().unwrap().push_str("init {\n");
            self.function_body.last_mut().unwrap().push_str("int __pid = 0;\n");
        } else if string_args .is_empty() {
            self.function_channels.last_mut().unwrap().push_str(&format!("proctype {} (chan ret; int __pid) {{\n", func_name));
        } else {
            let formatted_args = Self::format_arguments(&string_args , &sym_table);
            self.function_channels.last_mut().unwrap().push_str(&format!("proctype {} ({}; chan ret; int __pid) {{\n", func_name, &*formatted_args));
        }
        self.function_body.last_mut().unwrap().push_str("if\n::__pid==-1 -> __pid = _pid;\n::else->skip;\nfi;\n");

        // Only create a new symbol table if the function is not an anonymous function
        if self.function_body.len() == 1 {
            self.function_sym_table = sym_table;
        }
    }

    pub fn commit_function(&mut self) {
        // Commits the current function to the file
        // if self.init {
            // self.function_channels.last_mut().unwrap().push_str("__channel_hook\n");
        // }
        self.content.push_str(&self.function_channels.pop().unwrap());
        self.content.push_str(&self.function_metabody.pop().unwrap());
        self.content.push_str(&format!("{}}}\n\n", &*self.function_body.pop().unwrap()));

        // Only reset if the function is not an anonymous function
        if self.function_body.is_empty() {
            self.function_call_count = 0;
            self.function_messages = 0;
            self.random_count = 0;
            self.ltl_func = false;
            self.var_stack = Vec::new();
            self.array_var_stack = Vec::new();
            self.post_condition = String::new();
            self.init = false;
            self.parameterized_function = false;
            self.parameterized_vars = Vec::new();
        }
    }

    fn get_next_var(&mut self) -> String {
        if self.var_stack_p >= self.var_stack.last().unwrap().len() {
            self.var_stack_p = 0;
        }
        let var = self.var_stack.last().unwrap()[self.var_stack_p].clone();
        self.var_stack_p += 1;
        var
    }

    fn get_next_var_safe(&mut self) -> Option<String> {
        if self.var_stack.is_empty() {
            None
        } else {
            Some(self.get_next_var())
        }
    }

    pub fn write_function_call(&mut self, func_name: &str, call_arguments: &str, ret: bool, line_number: u32) {
        // Track how many function calls have taken place 
        // Create a channel for each
        // Name the receive variables appropriately
        // TODO determine return type    
        self.function_call_count += 1;
        let rendezvous = if self.var_stack.is_empty() {1} else {0}; 
        self.function_channels.last_mut().unwrap().push_str(&format!("chan ret{} = [{}] of {{ int }}; /*{}*/\n", self.function_call_count, rendezvous, line_number));
        
        // TODO make a mapping of variable name
        let call_arguments = call_arguments.replace('[', "(");
        let call_arguments = call_arguments.replace(']', "");
        let mut call_arguments = call_arguments.replace(':', "");

        // Foreach call argument which is an array, we pass by value and copy a new array
        let args_v: String = call_arguments.replace('(', "");
        let args_v: Vec<&str> = args_v.split(',').collect();
        for arg in args_v {
            if self.function_sym_table.contains(arg) {
                if let sym_table::SymbolType::Array(_, _) = self.function_sym_table.lookup(arg) {
                    self.function_body.last_mut().unwrap().push_str(&format!("int __temp_cp_arr_{};\n__copy_memory_to_next(__temp_cp_arr_{}, {});\n", self.arr_cp_count, self.arr_cp_count, arg));
                    call_arguments = call_arguments.replace(arg, &format!("__temp_cp_arr_{}", self.arr_cp_count));
                    self.arr_cp_count += 1;
                }
            }
        }

        // TODO determine if the function is returning
        let mut return_variable = format!("ret{}", self.function_call_count);
        let mut returning_call = false;
        if !self.var_stack.is_empty() {
            return_variable = self.get_next_var();
            self.function_body.last_mut().unwrap().push_str(&format!("{} = ", return_variable));
            returning_call = true; 
        } 
        if call_arguments.is_empty() {
            self.function_body.last_mut().unwrap().push_str(&format!("run {}(ret{}, __pid); /*{}*/\n", func_name, self.function_call_count, line_number));
        } else {
            self.function_body.last_mut().unwrap().push_str(&format!("run {}{}, ret{}, __pid); /*{}*/\n", func_name, call_arguments, self.function_call_count, line_number));
        }
        if returning_call {
            self.function_body.last_mut().unwrap().push_str(&format!("ret{} ? {}; /*{}*/\n", self.function_call_count, return_variable, line_number));
        }
        if ret && self.returning_function {
            self.function_body.last_mut().unwrap().push_str(&format!("int __ret_placeholder_{}; /*{}*/\n", self.function_call_count, line_number));
            self.function_body.last_mut().unwrap().push_str(&format!("{} ? __ret_placeholder_{}; /*{}*/\n", return_variable, self.function_call_count, line_number));
            self.function_body.last_mut().unwrap().push_str(&format!("ret ! __ret_placeholder_{}; /*{}*/\n", self.function_call_count, line_number));
            self.post_condition_check(0);
        } 
    }

    fn condition_to_string(expr: &formatted_condition::FormattedCondition) -> String {
        let symbol_map: HashMap<&str, &str> = [
            ("or", "||"),
            ("and", "&&"),
            (">=", ">="),
            ("<=", "<="),
            (">", ">"),
            ("<", "<"),
            ("==", "=="),
            ("!=", "!="),
            ("+", "+"),
            ("-", "-"),
            ("*", "*"),
            ("/", "/"),
            ("&&", "&&"),
            ("||", "||"),
        ].iter().cloned().collect();
        match expr {
            formatted_condition::FormattedCondition::Number(n) => n.to_string(),
            formatted_condition::FormattedCondition::Boolean(b) => {
                if *b {
                    String::from("true")
                } else {
                    String::from("false")
                }
            
            },
            formatted_condition::FormattedCondition::StringLiteral(s) => format!("\"{}\"", s),
            formatted_condition::FormattedCondition::Primitive(s) => format!("\"{}\"", s),
            formatted_condition::FormattedCondition::Variable(v) => v.clone(),
            formatted_condition::FormattedCondition::BinaryOperation(op, left, right) => {
                format!("({} {} {})", Self::condition_to_string(left), symbol_map.get(op).unwrap_or(&"Missing operator"), Self::condition_to_string(right))
            },
            formatted_condition::FormattedCondition::Not(inner) => {
                format!("!({})", Self::condition_to_string(inner))
            }
        }
    }

    pub fn write_if_condition(
        &mut self,
        condition: formatted_condition::FormattedCondition,
        line_number: u32
    ) {
        self.function_body.last_mut().unwrap().push_str("if\n");
        self.function_body.last_mut().unwrap().push_str(format!(":: {} -> /*{}*/\n", Self::condition_to_string(&condition), line_number).as_str());
    }

    pub fn write_pre_condition(
        &mut self,
        condition: formatted_condition::FormattedCondition,
        line_number: u32
    ) {
        self.function_body.last_mut().unwrap().push_str(format!("assert({}) /*{}*/ \n", Self::condition_to_string(&condition), line_number).as_str());
    }

    pub fn write_post_condition(
        &mut self,
        condition: formatted_condition::FormattedCondition,
    ) {
        self.post_condition = Self::condition_to_string(&condition);
    }

    pub fn write_else(&mut self) {
        self.function_body.last_mut().unwrap().push_str(":: else ->\n");
    }

    pub fn commit_if(&mut self) {
        self.function_body.last_mut().unwrap().push_str("fi;\n");
    }

    // Method to commit the content to the file and reset the string
    pub fn commit(&mut self) -> io::Result<()> {
        self.content.push_str(&format!("\n{}", self.ltl_specs));
        // Write header meta information
        // TODO: paramatise mailbox length and byte array lengths
        // TODO: use maximum_message_size to determine number of messages in list
        let unique_mtypes = self.mtype.iter().cloned().collect::<std::collections::HashSet<String>>().iter().cloned().collect::<Vec<String>>();
        let mut var_name = String::new();
        if !unique_mtypes.is_empty() {
            var_name = String::from(&format!("mtype = {{{}}};\n", unique_mtypes.join(",")));
        }
        // Messages
        var_name.push_str("typedef MessageType {\nbyte data1[2];\nint data2;\nbyte data3[2];\nbool data4;\n};\ntypedef\nMessageList {\nMessageType m1;\nMessageType m2;\nMessageType m3;\nMessageType m4;\nMessageType m5;\nMessageType m6;\n};\n\n");
        
        let mut mailbox_assignment = String::new();
        for mtype in unique_mtypes.iter() {
            var_name.push_str(&format!("chan __{} = [10] of {{ int, mtype, MessageList }};\n", mtype));
            // for i in 0..self.process_count + 1 { TODO wrong to use process_count
                // var_name.push_str(&format!("chan __p{}_{} = [3] of {{ int, mtype, MessageList }};\n", i, mtype));
            // }
            for i in 0..self.process_count + 1 {
                mailbox_assignment.push_str(&format!("__{}[{}] = __p{}_{};\n", mtype, i, i, mtype));
            }
        }
        // self.content = self.content.replace("__channel_hook\n", &mailbox_assignment);

        // TODO remove or refactor Elixir list c_decl
        // let typ = "int";
        // var_name.push_str(&format!("c_decl {{\ntypedef struct LinkedList {{\n{} val;\nstruct LinkedList *next;\n}} LinkedList;\n\nLinkedList* newLinkedList({} val) {{\nLinkedList *newNode = (LinkedList *)malloc(sizeof(LinkedList));\nnewNode->val = val;\nnewNode->next = NULL;\nreturn newNode;\n}};\n\nLinkedList* prepend(LinkedList *head, {} val) {{\nLinkedList *newNode = (LinkedList *)malloc(sizeof(LinkedList));\nnewNode->val = val;\nnewNode->next = head;\nreturn newNode;\n}};\n\nLinkedList* append(LinkedList *head, {} vals[], size_t size) {{\nLinkedList *newNode = head;\nfor ({} i = 0; i < size; i++) {{\nnewNode->next = newLinkedList(vals[i]);\nnewNode = newNode->next;\n}};\nreturn head;\n}};\n}}\n\n", typ, typ, typ, typ, typ));
        // ltl specs
        var_name = add_linked_list_boiler_plate(var_name);
        var_name.push_str(&format!("{}\n", self.ltl_header));
        let header_buf = var_name
            .as_bytes();

        let _ = self.file.write_all(header_buf);
        // Write parsed content
        self.file.write_all(self.content.as_bytes())?;
        self.content.clear(); // Reset the string
        Ok(())
    }

    pub fn write_number(&mut self, number: &str, ret: bool) {
        if ret && self.returning_function {
            self.function_body.last_mut().unwrap().push_str(&format!("ret ! {}; /*{}*/\n", number, 0));
            self.post_condition_check(0);
        } else if !self.var_stack.is_empty() {
            let var = self.get_next_var();
            if !self.ltl_vars.contains(&var) {
                self.function_sym_table.add_entry(var.clone(), sym_table::SymbolType::Integer);
                let last_body = self.function_body.pop().unwrap();
                self.function_body.push(last_body.replace(&format!("int {};\n", var), ""));
            }
            if self.parameterized_function && self.parameterized_model && self.parameterized_vars.contains(&var.to_string()) {
                if self.ltl_vars.contains(&var) {
                    self.ltl_header.push_str(&format!("int {} = {};\n", var, number));
                } else {
                    self.function_body.last_mut().unwrap().push_str(&format!("int {} = {};\n", var, PARAM_STR));
                }
            } else if !self.ltl_vars.contains(&var) {
                self.function_body.last_mut().unwrap().push_str(&format!("int {} = {};\n", var, number));
            } else {
                self.function_body.last_mut().unwrap().push_str(&format!("{} = {};\n", var, number));
            }
        } else {   
            self.function_body.last_mut().unwrap().push_str(number);
        }
    }

    pub fn write_boolean(&mut self, val: &str, ret: bool) {
        if ret && self.returning_function {
            self.function_body.last_mut().unwrap().push_str(&format!("ret ! {}; /*{}*/\n", val, 0));
            self.post_condition_check(0);
        } else if !self.var_stack.is_empty() {
            let assignee = self.get_next_var();
            if self.parameterized_function && self.parameterized_model && self.parameterized_vars.contains(&assignee.to_string()) {
                self.function_body.last_mut().unwrap().push_str(&format!("{} = {};\n", assignee, PARAM_STR));
            } else {
                self.function_body.last_mut().unwrap().push_str(&format!("{} = {}; /*{}*/\n", assignee, val, 0));
            }
        } else if !self.array_var_stack.is_empty() {
            // TODO
            error!("Cannot write booleans to arrays.")
        } 
        else {
            self.function_body.last_mut().unwrap().push_str(&format!("{} /*{}*/\n", val, 0));
        }
    }

    pub fn write_primitive(&mut self, primitive: &str, ret: bool, line_number: u32) {
        let formatted_string = if ret && self.returning_function {
            self.post_condition_check(0);
            format!("ret ! {}; /*{}*/\n", primitive, line_number)
        } else if !self.var_stack.is_empty() {
            let assignee = self.get_next_var();
            if self.parameterized_function && self.parameterized_model && self.parameterized_vars.contains(&assignee.to_string()) {
                format!("{} = {};\n", assignee, PARAM_STR)
            } else {
                format!("{} = {};\n", assignee, primitive)
            }
        } else {
            format!("{} /*{}*/\n", primitive, line_number)
        };
        self.function_body.last_mut().unwrap().push_str(&formatted_string);
        
    }

    pub fn write_assignment_variable(&mut self, var: &str, typ: sym_table::SymbolType, block_assignment: bool) {
        self.block_assignment = block_assignment;
        let formatted_var: &String = &format!("int {};\n", var);
        if self.ltl_func && self.ltl_vars.contains(&var.to_string()) {
            if !self.used_ltl_vars.contains(&var.to_string()) {
                self.ltl_header.push_str(&formatted_var.clone());
                self.used_ltl_vars.push(var.to_string());
            }
        } else if !self.function_sym_table.contains(var) {
            self.function_body.last_mut().unwrap().push_str(formatted_var);
        }
        if !block_assignment {
            // TODO Verify
            // self.function_body.last_mut().unwrap().push_str(&format!("atomic {{\n"));
        }

        // Push the variable name to the stack to be applied
        self.var_stack.push(vec![String::from(var)]);
        if !self.function_sym_table.contains(var) {
            self.function_sym_table.add_entry(String::from(var), typ);
        }
    }

    pub fn write_assignment_tuple(&mut self, vars: Vec<String>, typ: sym_table::SymbolType) {
        // self.function_body.last_mut().unwrap().push_str(&format!("atomic {{\n"));
        let mut var_names = Vec::new();
        for var in vars {
            // TODO, for now only integer
            if !self.function_sym_table.contains(&var.clone()) {
                self.function_body.last_mut().unwrap().push_str(&format!("int {};\n", var.clone()));
                self.function_sym_table.add_entry(var.clone(), sym_table::SymbolType::Integer);
            } 
            var_names.push(var);
        };
        self.var_stack.push(var_names);
    }

    pub fn commit_assignment(&mut self) {
        self.var_stack.pop();
        self.var_stack_p = 0;
    }

    pub fn commit_statement_assignment(&mut self) {
        self.var_stack.pop();
        self.var_stack_p = 0;
        self.block_assignment = false;
    }

    pub fn write_spawn_process(&mut self, proctype: &str, args: &str, line_number: u32) {
        self.process_count += 1;
        self.function_call_count += 1;
        self.function_channels.last_mut().unwrap().push_str(&format!("chan ret{} = [1] of {{ int }};\n", self.function_call_count));

        // Format args depending on if they are empty
        let formatted_args = format!("{}{}ret{},-1", args, if args.is_empty() {""} else {","}, self.function_call_count);

        // TODO verify logic, is a stack appropriate
        self.function_body.last_mut().unwrap().push_str("atomic {\n");
        let var_name = self.get_next_var_safe();
        let i = self.process_count;
        let assignee = if let Some(x) = var_name {
            // Add to the lookup tables
            self.process_name.insert(i, x.clone());
            self.mailbox_id.insert(x.clone(), i);
            x
        } else {
            self.function_body.last_mut().unwrap().push_str("int __tmp_pid;\n");
            String::from("__tmp_pid")
        };
        self.function_body.last_mut().unwrap().push_str(&format!("{} = run {}({}); /*{}*/\n}}\n", assignee, proctype, formatted_args, line_number));
    }

    pub fn write_send(&mut self, mut target: &str, mut args: Vec<String>, line_number: u32) {
        let mailbox: i32 = *self.mailbox_id.get(target).unwrap_or(&-1);
        let mtype = args.remove(0).replace(':', "").to_uppercase();
        self.mtype.push(mtype.clone());
        
        // Edge case, sending to self
        target = if target == "self" { "__pid" } else { target };

        // Create the message component
        let mut i = 1;
        let mut data = 2;

        // Replace list args with dummy variable
        for arg in args.iter_mut() {
            if self.function_sym_table.contains(arg) {
                if let sym_table::SymbolType::Array(_, _) = self.function_sym_table.lookup(arg) {
                    let arg_old = arg.clone();
                    *arg = format!("__temp_cp_arr_{}", self.arr_cp_count);
                    self.function_body.last_mut().unwrap().push_str(&format!("int __temp_cp_arr_{};\n__copy_memory_to_next(__temp_cp_arr_{}, {});\n", self.arr_cp_count, self.arr_cp_count, arg_old));
                    self.arr_cp_count += 1;
                }
            }
        }
        self.function_body.last_mut().unwrap().push_str(&format!("MessageList msg_{}; /*{}*/\n", self.function_messages, line_number));
        for mut arg in args {
            // TODO: replace third argument with type
            if arg.starts_with("{:self,") {
                arg = String::from("__pid");
            } else if arg.starts_with(':') {
                // Now an mtype
                arg = arg.replace(':', "").to_uppercase();
                self.mtype.push(arg.clone());
                data = 2;
            } else if self.function_sym_table.contains(&arg) && self.function_sym_table.lookup(&arg) == &sym_table::SymbolType::Atom {
                arg = arg.replace(':', "");
                data = 2;
            }

            self.function_body.last_mut().unwrap().push_str(&format!("msg_{}.m{}.data{} = {}; /*{}*/\n", self.function_messages, i, data, arg, line_number));
            i += 1;
        }
        if mailbox == -1 {
            if self.skip_bounded {
                self.function_body.last_mut().unwrap().push_str(&format!("if /*{}*/\n:: nfull(__{}) -> __{} !! {},{}, msg_{}; /*{}*/\n:: full(__{}) -> skip; /*{}*/\nfi /*{}*/\n", line_number, target, target, mtype, target, self.function_messages, line_number, mtype, line_number, line_number));
            } else {
                self.function_body.last_mut().unwrap().push_str(&format!("__{} !! {},{}, msg_{}; /*{}*/\n", mtype, target, mtype, self.function_messages, line_number));
            }
        } else if self.skip_bounded {
            self.function_body.last_mut().unwrap().push_str(&format!("if /*{}*/\n:: nfull(__{}) -> __{} !! {},{}, msg_{}; /*{}*/\n:: full(__{}) -> skip; /*{}*/\nfi /*{}*/\n", line_number, mtype, mtype, mailbox, mtype, self.function_messages, line_number, mtype, line_number, line_number));
        } else {
            self.function_body.last_mut().unwrap().push_str(&format!("__{} !! {},{}, msg_{}; /*{}*/\n", mtype, target, mtype, self.function_messages, line_number));
        }
        self.function_messages += 1;
    }

    pub fn write_receive(&mut self, line_number: u32) {
        self.function_body.last_mut().unwrap().push_str(&format!("MessageList rec_v_{}; /*{}*/\n", self.receive_count, line_number));
        self.function_body.last_mut().unwrap().push_str(&format!("do /*{}*/\n", line_number));
        self.receive_count += 1;
    }

    pub fn commit_receive(&mut self, _line_number: u32) {
        self.function_body.last_mut().unwrap().push_str("od;\n");
        
    }

    pub fn write_receive_assignment(&mut self, assignments: Vec<String>, line_number: u32) {
        // First element is the message type
        for (i, assignment) in assignments.iter().enumerate() {
            if i == 0 {
                let mtype = assignment.replace(':', "").to_uppercase();
                self.mtype.push(mtype.clone());
                // self.function_body.last_mut().unwrap().push_str(&format!(":: messageType == {} -> /*{}*/\n", assignment.to_uppercase(), line_number));
                self.function_body.last_mut().unwrap().push_str(&format!(":: __{} ?? eval(__pid),{}, rec_v_{} -> /*{}*/\n", mtype, mtype, self.receive_count-1, line_number));
                
            } else if self.ltl_vars.contains(assignment) {
                if !self.used_ltl_vars.contains(assignment) {
                    self.ltl_header.push_str(&format!("int {}; /*{}*/\n", assignment, line_number));
                    self.used_ltl_vars.push(assignment.clone());
                }
                self.function_sym_table.add_entry(String::from(assignment), sym_table::SymbolType::Atom);
                self.function_body.last_mut().unwrap().push_str(&format!("{} = rec_v_{}.m{}.{}; /*{}*/\n", assignment, self.receive_count - 1, i, "data2", line_number)); 
            } else if !assignment.starts_with(':') {
                if !self.function_sym_table.contains(assignment) {
                    self.function_body.last_mut().unwrap().push_str(&format!("int {}; /*{}*/\n", assignment, line_number));
                    self.function_sym_table.add_entry(String::from(assignment), sym_table::SymbolType::Integer);
                }
                self.function_body.last_mut().unwrap().push_str(&format!("{} = rec_v_{}.m{}.{}; /*{}*/\n", assignment, self.receive_count - 1, i, "data2", line_number));
            } else {
                let var = assignment.replace(':', "");
                self.mtype.push(var.clone().to_uppercase());
                self.function_body.last_mut().unwrap().push_str(&format!("int {}; /*{}*/\n", var, line_number));
                self.function_sym_table.add_entry(String::from(assignment), sym_table::SymbolType::Atom);
                self.function_body.last_mut().unwrap().push_str(&format!("{} = rec_v_{}.m{}.{}; /*{}*/\n", var, self.receive_count - 1, i, "data2", line_number));
            }
        }
    }

    pub fn write_receive_multi_atom(&mut self, mtype: String, atom: String, line_number: u32) {
        self.function_body.last_mut().unwrap().push_str(&format!(":: __{} ?? eval(__pid),{}, {} -> /*{}*/\n", mtype.to_uppercase(), mtype.to_uppercase(), atom, line_number));
    }
    
    pub fn write_end_receive_statement(&mut self) {
        self.function_body.last_mut().unwrap().push_str("break;\n");
    }

    pub fn write_io(&mut self, io_put: &str) {
        self.function_body.last_mut().unwrap().push_str(&format!("printf(\"{}\\n\");\n", io_put));
    }

    pub fn start_unless(&mut self) {
        self.function_body.last_mut().unwrap().push_str("{\n")
    }

    pub fn write_unless_condition(
        &mut self,
        condition: formatted_condition::FormattedCondition
    ) {
        self.function_body.last_mut().unwrap().push_str("}\nunless\n{");
        self.function_body.last_mut().unwrap().push_str(format!("{}\n", Self::condition_to_string(&condition)).as_str());
        self.function_body.last_mut().unwrap().push_str("}\n")
    }

    pub fn write_assigned_variable(
        &mut self,
        var: &str,
        ret: bool,
        line_number: u32
    ) {
        if ret && self.returning_function {
            self.function_body.last_mut().unwrap().push_str(&format!("ret ! {}; /*{}*/\n", var, line_number));
            self.post_condition_check(0);
        } else if self.block_assignment && !self.var_stack.is_empty() {
            let assignee = self.get_next_var();
            self.function_body.last_mut().unwrap().push_str(&format!("{} = {}; /*{}*/\n", assignee, var, line_number));
        } else if let Some(x) = self.get_next_var_safe() {
            self.function_body.last_mut().unwrap().push_str(&format!("{} = {}; /*{}*/\n", x, var, line_number)); 
        } else {
            println!("Trying to write {} might not make sense", var);
            self.function_body.last_mut().unwrap().push_str(&format!("{} /*{}*/\n", var, line_number));
        }
    }

    pub fn write_ltl(
        &mut self,
        spec: &str
    ) {
        self.ltl_func = true;
        self.ltl_count += 1;
        self.ltl_specs.push_str(&format!("ltl ltl_{} {{ {} }};\n", self.ltl_count, spec));
    }

    pub fn ltl_count(
        self,
    ) -> i32 {
        self.ltl_count
    }

    pub fn write_defmodule(
        &mut self,
        module: &str
    ) {
        self.module = module.to_string();
    }

    pub fn write_array_assignment(
        &mut self,
        var: &str,
        typ: sym_table::SymbolType,
        block_assignment: bool
    ) {
        self.block_assignment = block_assignment;
        self.function_body.last_mut().unwrap().push_str(&format!("int {};\n__get_next_memory_allocation({});\n", var, var));
        self.array_var_stack.push(var.to_string());
        self.function_sym_table.add_entry(var.to_string(), SymbolType::Array(Box::from(SymbolType::Integer), 0));
    }

    pub fn write_array(
        &mut self,
        elements: Vec<String>,
    ) {
        // For an assignment, we can take the var off the stack
        if let Some(var) = self.array_var_stack.pop() {
            let mut i = 0;
            for element in elements {
                // Check if the element type is an array
                if let Some(sym_table::SymbolType::Array(_, size)) = self.function_sym_table.safe_lookup(&element) {
                    self.function_body.last_mut().unwrap().push_str(&format!("__list_append_list({}, {});\n", var, element));
                    i += 1;
                } else {
                    self.function_body.last_mut().unwrap().push_str(&format!("__list_append({}, {});\n", var, element));
                    i += 1;
                }
            };
            // Replace the existing symbol table entry with the size and same type as var
            self.function_sym_table.update_array_size(&var, i);
        } 
    }

    pub fn write_array_read(
        &mut self,
        assignees: Vec<String>,
        assignment: String,
    ) {
        for (i, assignee) in assignees.iter().enumerate() {
            self.function_body.last_mut().unwrap().push_str(&format!("int {};\n", assignee));
            self.function_body.last_mut().unwrap().push_str(&format!("{} = __list_at({}, {});\n", assignee, assignment, i));
        }
    }

    pub fn write_basic_for_loop(
        &mut self,
        iterator: &str,
        iterable: &str,
    ) {
        self.function_body.last_mut().unwrap().push_str(&format!(
            "atomic {{\n\
                __list_ptr = 0;\n\
                __list_ptr_new = 0;\n\
                do\n\
                :: __list_ptr >= LIST_LIMIT || __list_ptr_new >= LIST_LIMIT -> break;\n\
                :: else ->\n\
                    if\n\
                    :: LIST_ALLOCATED({}, __list_ptr) ->\n\
        ", iterable));
        if iterator != "_" {
            if !self.function_sym_table.contains(iterator) {
                self.function_body.last_mut().unwrap().push_str(&format!("int {};\n", iterator));
                self.function_sym_table.add_entry(iterator.to_string(), sym_table::SymbolType::Integer);
            }
            self.function_body.last_mut().unwrap().push_str(&format!("{} = LIST_VAL({}, __list_ptr);\n", iterator, iterable));
        };
        if !self.array_var_stack.is_empty() {
            let var = self.array_var_stack.pop().unwrap();
            self.function_sym_table.add_entry(var.clone(), SymbolType::Array(Box::from(SymbolType::Integer), 0));
            self.function_body.last_mut().unwrap().push_str(&format!("LIST_ALLOCATED({}, __list_ptr_new) = true;\n", var));
            let new_var = format!("LIST_VAL({}, __list_ptr_new)", var);
            self.var_stack.push(vec![new_var]);
        };
    }

    pub fn commit_for_loop(
        &mut self,
        iterator: String,
    ) {
        self.function_body.last_mut().unwrap().push_str(";\n\
            __list_ptr_new++;\n\
            __list_ptr++;\n\
            :: else -> __list_ptr++;\n\
            fi\n\
        od\n\
        }\n");
        self.function_sym_table.remove_entry(&iterator);
        if !self.array_var_stack.is_empty() {
            self.var_stack.pop();
        }
    }

    pub fn write_range_for_loop(
        &mut self,
        mut iterator: &str,
        n1: &str,
        n2: &str,
        line_number: u32,
    ) {
        if iterator != "_" {
            if !self.function_sym_table.contains(iterator) {
                self.function_body.last_mut().unwrap().push_str(&format!("int {};\n", iterator));
                self.function_sym_table.add_entry(iterator.to_string(), sym_table::SymbolType::Integer);
            }
        } else {
            iterator = "__dummy_iterator";
        }
        self.function_body.last_mut().unwrap().push_str(&format!("for({} : {} .. {}) {{ /*{}*/\n", iterator, n1, n2, line_number));
        if (self.block_assignment) {
            let var = self.array_var_stack.last().unwrap();
            self.function_sym_table.add_entry(var.clone(), SymbolType::Array(Box::from(SymbolType::Integer), 0));
            self.function_body.last_mut().unwrap().push_str(&format!("LIST_ALLOCATED({}, {}) = true;\n", var, iterator));
            let new_var = format!("LIST_VAL({}, {})", var, iterator);
            self.var_stack.push(vec![new_var]);
        } else {
            println!("Do something?");
        }
    }

    pub fn commit_range_for_loop(
        &mut self,
    ) {
        if self.block_assignment {
            self.var_stack.pop();
        }
        self.function_body.last_mut().unwrap().push_str("}\n");

    }

    pub fn write_enum_random(
        &mut self,
        args: Vec<String>,
    ) {
        // TODO only pseudorandom as Promela does not support randomness
        let array = &args[0];
        let assignee = self.get_next_var();
        self.function_body.last_mut().unwrap().push_str(&format!("__list_random({}, {});\n", array, assignee));
        warn!("Random number generation is not supported in Promela");
    }

    pub fn write_enum_at(
        &mut self,
        args: Vec<String>,
    ) {
        let list = &args[0];
        let index = &args[1];
        if let Some(x) = self.get_next_var_safe() {
            self.function_body.last_mut().unwrap().push_str(&format!("{} = ", x));
        }
        self.function_body.last_mut().unwrap().push_str(&format!("__list_at({}, {})\n", list, index));
    }
    
    pub fn write_enum_map(
        &mut self,
        iterable: String,
        fn_args: Vec<String>,
        assignee: String,
    ) {
        let size = sym_table::get_array_size(self.function_sym_table.lookup(&iterable));
        let typ = Self::type_to_str(sym_table::get_array_inner_type(self.function_sym_table.lookup(&iterable)));
        self.function_sym_table.update_array_size(&assignee, size);
        
        // TODO only supports single argument functions for now
        if fn_args.len() != 1 {
            panic!("Enum map only supports single argument functions");
        }
        let arg = &fn_args[0];
        self.function_channels.last_mut().unwrap().push_str(&format!("chan __anonymous_ret_{} = [0] of {{ int }};\n", self.anonymous_function_count));
        self.function_body.last_mut().unwrap().push_str(&format!(
            "atomic {{\n\
                int __iter;\n\
                __iter = 0;\n\
                do\n\
                :: __iter >= LIST_LIMIT -> break;\n\
                :: else ->\n\
                    if\n\
                    :: LIST_ALLOCATED({}, __iter) ->\n\
                    run __anonymous_{}(LIST_VAL({}, __iter),__anonymous_ret_{},__pid);\n\
                    LIST_ALLOCATED({}, __iter) = true;\n\
                    __anonymous_ret_{} ? LIST_VAL({}, __iter);\n\
                    __iter++;\n\
                    :: else -> __iter++;\n\
                    fi\n\
                od\n\
            }}\n"
        , iterable, self.anonymous_function_count, iterable, self.anonymous_function_count, assignee, self.anonymous_function_count, assignee));
        
        let mut anonymous_sym_table = sym_table::SymbolTable::new();
        // TODO only supports integer arguments for now
        anonymous_sym_table.add_entry(arg.to_string(), sym_table::SymbolType::Integer);
        self.new_function(&format!("__anonymous_{}", self.anonymous_function_count), &arg.to_string(), anonymous_sym_table, false, Vec::new(), Vec::new());
        self.anonymous_function_count += 1;
    }

    pub fn commit_enum_map(
        &mut self,
    ) {
        self.commit_function();
    }

    pub fn write_case(&mut self, _line_number: u32) {
        self.function_body.last_mut().unwrap().push_str("do\n");
    }

    pub fn write_case_statement(&mut self, var: String, cmp: String) {
        if cmp.contains(':') {
            self.function_body.last_mut().unwrap().push_str(&format!(":: {} == {} ->\n", var, cmp.replace(':', "").to_uppercase()));
        } else {
            self.function_body.last_mut().unwrap().push_str(&format!(":: {} == {} ->\n", var, cmp));
        }
    }

    pub fn commit_case(&mut self) {
        self.function_body.last_mut().unwrap().push_str("od\n");
    }

    pub fn mark_paramaterized(&mut self, vars: Vec<String>) {
        self.parameterized_function = true;
        self.parameterized_vars = vars;
    }

    fn get_vars_from_condition(condition: &formatted_condition::FormattedCondition) -> Vec<String> {
        let mut vars = Vec::new();
        match condition {
            formatted_condition::FormattedCondition::Variable(v) => vars.push(v.clone().as_str().to_string()),
            formatted_condition::FormattedCondition::BinaryOperation(_, left, right) => {
                vars.extend(Self::get_vars_from_condition(left));
                vars.extend(Self::get_vars_from_condition(right));
            },
            formatted_condition::FormattedCondition::Not(inner) => {
                vars.extend(Self::get_vars_from_condition(inner));
            },
            _ => (),
        };
        vars
    }

    fn move_var_to_global(&mut self, var: String) {
        // Find the variable in the local symbol table
        if self.used_ltl_vars.contains(&var) {
            return;
        }
        let typ = self.function_sym_table.safe_lookup(&var);
        if typ.is_none() {
            // Assumed to be an int
            let str = &format!("int {};\n", var);
            self.ltl_header.push_str(str);
            self.function_sym_table.add_entry(var.clone(), sym_table::SymbolType::Integer);
            self.used_ltl_vars.push(var);            
            return;
        }
        let typ = typ.unwrap();
        match typ {
            sym_table::SymbolType::Integer => {
                // Find the line with the variable declaration, format: int var...
                // Format is something like int var; or int var = 0;
                let search_term = &format!("int {}", var);
                self.move_int_to_global(search_term, var.clone());
                self.used_ltl_vars.push(var);
            },
            sym_table::SymbolType::Boolean => {
                let str = &format!("bool {};\n", var);
                self.ltl_header.push_str(str);
                let last_body = self.function_body.pop().unwrap();
                self.function_body.push(last_body.replace(str, ""));
                self.used_ltl_vars.push(var);
            },
            _ => (),
        }
    }

    fn move_int_to_global(&mut self, search_term: &str, var: String) {
        // Create a regex pattern to match "int var = number;" or "int var;"
        let pattern = format!(r"(?m)^\s*{}(?: = (\d+|{}))?;\s*$\n?", search_term, PARAM_STR);
        let re = Regex::new(&pattern).unwrap();
        let last_body = self.function_body.pop().unwrap();

        // Find and extract the number from the string
        if let Some(captures) = re.captures(&last_body) {
            let mut number = 0;
            if let Some(matched) = captures.get(1) {
                if matched.as_str() == PARAM_STR {
                    if !self.ltl_header.contains(&format!("int {}", var)) {
                        self.ltl_header.push_str(&format!("int {} = {};\n", var, PARAM_STR));
                    }
                } else {
                    number = matched.as_str().parse().unwrap();
                    self.ltl_header.push_str(&format!("{} = {};\n", search_term, number));
                }
            } 

            // Remove the entire line containing the pattern
            let result_string = re.replace_all(&last_body, "").to_string();
            self.function_body.push(result_string);
        } else if last_body.contains(search_term) {
            self.ltl_header.push_str(&format!("int {};\n", var));
            self.function_body.push(last_body.replace(search_term, ""));
        } else {
            self.function_body.push(last_body);
        }
    }

    pub fn write_predicate(&mut self, predicate_name: String, condition: &formatted_condition::FormattedCondition) {
        let vars = Self::get_vars_from_condition(condition);
        for var in vars {
            self.move_var_to_global(var);
        }
        self.ltl_header.push_str(&format!("#define {} ({})\n", predicate_name, Self::condition_to_string(condition)));
    }
}