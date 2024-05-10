use std::borrow::Borrow;
use std::fs::File;
use std::collections::HashMap;

use std::io::{self, Write};

use log::warn;

use crate::formatted_condition;
use crate::internal_representation::sym_table::{self, get_array_size};
use crate::internal_representation::boilerplate::add_linked_list_boiler_plate;

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
    var_stack: Vec<String>,
    mtype: Vec<String>,
    _maximum_message_size: u32,
    function_messages: u32,
    receive_count: u32,
    ltl_count: u32,
    file: File,
    module: String,
    array_capacity: u32,
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
}

impl FileWriter {
    // Constructor method to create a new instance
    pub fn new(file_path: &str, skip_bounded: bool) -> io::Result<Self> {
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
            mtype: Vec::new(),
            _maximum_message_size: 1,
            function_messages: 0,
            receive_count: 0,
            ltl_count: 0,
            file,
            module: String::new(),
            array_capacity: 100,
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
        if self.init {
            self.function_channels.last_mut().unwrap().push_str("__channel_hook\n");
        }
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
            self.post_condition = String::new();
            self.init=false;
        }
    }

    pub fn write_function_call(&mut self, func_name: &str, call_arguments: &str, ret: bool, line_number: u32) {
        // Track how many function calls have taken place 
        // Create a channel for each
        // Name the receive variables appropriately
        // TODO determine return type    
        self.function_call_count += 1;
        self.function_channels.last_mut().unwrap().push_str(&format!("chan ret{} = [1] of {{ int }}; /*{}*/\n", self.function_call_count, line_number));
        
        // TODO make a mapping of variable name
        let call_arguments = call_arguments.replace('[', "(");
        let call_arguments = call_arguments.replace(']', "");

        // TODO determine if the function is returning
        let mut return_variable = format!("ret{}", self.function_call_count);
        let mut returning_call = false;
        if !self.var_stack.is_empty() {
            return_variable = self.var_stack.last().unwrap().to_string();
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
            self.post_condition_check(0);
            self.function_body.last_mut().unwrap().push_str(&format!("int __ret_placeholder_{}; /*{}*/\n", self.function_call_count, line_number));
            self.function_body.last_mut().unwrap().push_str(&format!("{} ? __ret_placeholder_{}; /*{}*/\n", return_variable, self.function_call_count, line_number));
            self.function_body.last_mut().unwrap().push_str(&format!("ret ! __ret_placeholder_{}; /*{}*/\n", self.function_call_count, line_number));
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
        var_name.push_str("typedef MessageType {\nbyte data1[20];\nint data2;\nbyte data3[20];\nbool data4;\n};\ntypedef\nMessageList {\nMessageType m1;\nMessageType m2;\nMessageType m3;\nMessageType m4;\nMessageType m5;\nMessageType m6;\n};\n\n");
        
        let mut mailbox_assignment = String::new();
        for mtype in unique_mtypes.iter() {
            var_name.push_str(&format!("chan __{}[{}] = [10] of {{ mtype, MessageList }};\n", mtype, self.max_process_count));
            for i in 0..self.process_count + 1 {
                var_name.push_str(&format!("chan __p{}_{} = [10] of {{ mtype, MessageList }};\n", i, mtype));
            }
            for i in 0..self.process_count + 1 {
                mailbox_assignment.push_str(&format!("__{}[{}] = __p{}_{};\n", mtype, i, i, mtype));
            }
        }
        self.content = self.content.replace("__channel_hook\n", &mailbox_assignment);

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

    pub fn write_number(&mut self, number: &str) {
        self.function_body.last_mut().unwrap().push_str(number);
    }

    pub fn write_primitive(&mut self, primitive: &str, ret: bool, line_number: u32) {
        let formatted_string = if ret && self.returning_function {
            self.post_condition_check(0);
            format!("ret ! {}; /*{}*/\n", primitive, line_number)
        } else if self.block_assignment {
            format!("{} = {};", self.var_stack.last().unwrap(), primitive)
        } else {
            format!("{} /*{}*/\n", primitive, line_number)
        };
        self.function_body.last_mut().unwrap().push_str(&formatted_string);
        
    }

    pub fn write_assignment_variable(&mut self, var: &str, typ: sym_table::SymbolType, block_assignment: bool) {
        self.block_assignment = block_assignment;
        let formatted_var = &format!("int {};\n", var);
        if self.ltl_func && self.ltl_vars.contains(&var.to_string()) {
            if !self.used_ltl_vars.contains(&var.to_string()) {
                self.ltl_header.push_str(&formatted_var.clone());
                self.used_ltl_vars.push(var.to_string());
            }
        } else if !self.function_sym_table.contains(var) {
            self.function_body.last_mut().unwrap().push_str(formatted_var);
        }
        if !block_assignment {
            
            self.function_body.last_mut().unwrap().push_str(&format!("atomic {{\n{} = ", var));
        }

        // Push the variable name to the stack to be applied by spawn
        self.var_stack.push(String::from(var));
        self.function_sym_table.add_entry(String::from(var), typ);
    }

    pub fn commit_assignment(&mut self) {
        self.var_stack.pop();
        self.function_body.last_mut().unwrap().push_str(";\n}\n");
    }

    pub fn commit_statement_assignment(&mut self) {
        self.var_stack.pop();
        self.block_assignment = false;
    }

    pub fn write_spawn_process(&mut self, proctype: &str, args: &str, line_number: u32) {
        self.process_count += 1;
        self.function_call_count += 1;
        self.function_channels.last_mut().unwrap().push_str(&format!("chan ret{} = [1] of {{ int }};\n", self.function_call_count));

        // Format args depending on if they are empty
        let formatted_args = format!("{}{}ret{},-1", args, if args.is_empty() {""} else {","}, self.function_call_count);

        // TODO verify logic, is a stack appropriate
        let var_name = self.var_stack.last();
        let i = self.process_count;
        if let Some(x) = var_name {
            // Add to the lookup tables
            self.process_name.insert(i, x.clone());
            self.mailbox_id.insert(x.clone(), i);
        }
        // Create a mailbox for each process
        self.function_body.last_mut().unwrap().push_str(&format!("run {}({}); /*{}*/\n", proctype, formatted_args, line_number));
    }

    pub fn write_send(&mut self, mut target: &str, mut args: Vec<String>, line_number: u32) {
        let mailbox: i32 = *self.mailbox_id.get(target).unwrap_or(&-1);
        let mtype = args.remove(0).replace(':', "").to_uppercase();
        self.mtype.push(mtype.clone());
        
        // Edge case, sending to self
        target = if target == "self" { "__pid" } else { target };

        // Create the message component
        let mut i = 1;
        self.function_body.last_mut().unwrap().push_str(&format!("MessageList msg_{}; /*{}*/\n", self.function_messages, line_number));
        for mut arg in args {
            // TODO: replace third argument with type
            if arg.starts_with("{:self,") {
                arg = String::from("__pid");
            }

            self.function_body.last_mut().unwrap().push_str(&format!("msg_{}.m{}.data{} = {}; /*{}*/\n", self.function_messages, i, 2, arg, line_number));
            i += 1;
        }
        if mailbox == -1 {
            if self.skip_bounded {
                self.function_body.last_mut().unwrap().push_str(&format!("if /*{}*/\n:: nfull(__{}[{}]) -> __{}[{}] ! {}, msg_{}; /*{}*/\n:: full(__{}[{}]) -> skip; /*{}*/\nfi /*{}*/\n", line_number, mtype, target, mtype, target, mtype, self.function_messages, line_number, mtype, target, line_number, line_number));
            } else {
                self.function_body.last_mut().unwrap().push_str(&format!("__{}[{}] ! {}, msg_{}; /*{}*/\n", mtype, target, mtype, self.function_messages, line_number));
            }
        } else if self.skip_bounded {
            self.function_body.last_mut().unwrap().push_str(&format!("if /*{}*/\n:: nfull(__{}[{}]) -> __{}[{}] ! {}, msg_{}; /*{}*/\n:: full(__{}[{}]) -> skip; /*{}*/\nfi /*{}*/\n", line_number, mtype, mailbox, mtype, mailbox, mtype, self.function_messages, line_number, mtype, mailbox, line_number, line_number));
        } else {
            self.function_body.last_mut().unwrap().push_str(&format!("__{}[{}] ! {}, msg_{}; /*{}*/\n", mtype, target, mtype, self.function_messages, line_number));
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
                self.mtype.push(assignment.to_uppercase());
                // self.function_body.last_mut().unwrap().push_str(&format!(":: messageType == {} -> /*{}*/\n", assignment.to_uppercase(), line_number));
                self.function_body.last_mut().unwrap().push_str(&format!(":: __{}[__pid] ? {}, rec_v_{} -> /*{}*/\n", assignment.to_uppercase(), assignment.to_uppercase(), self.receive_count-1, line_number));
                
            } else {
                self.function_body.last_mut().unwrap().push_str(&format!("int {}; /*{}*/\n", assignment, line_number));
                self.function_body.last_mut().unwrap().push_str(&format!("{} = rec_v_{}.m{}.{}; /*{}*/\n", assignment, self.receive_count - 1, i, "data2", line_number));
            }
        }
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
            self.post_condition_check(0);
            self.function_body.last_mut().unwrap().push_str(&format!("ret ! {}; /*{}*/\n", var, line_number));
        } else if self.block_assignment {
            self.function_body.last_mut().unwrap().push_str(&format!("{} = {}; /*{}*/\n", self.var_stack.last().unwrap(), var, line_number));
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
        self.ltl_specs.push_str(&format!("ltl ltl_{} {{ {} }};", self.ltl_count, spec));
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
    ) {
        self.function_body.last_mut().unwrap().push_str(&format!("linked_list {};\n", var));
        self.array_var_stack.push(var.to_string());
        self.function_sym_table.add_entry(var.to_string(), typ);
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
            self.function_body.last_mut().unwrap().push_str(&format!("int {};\n", iterator));
            self.function_body.last_mut().unwrap().push_str(&format!("{} = LIST_VAL({}, __list_ptr);\n", iterator, iterable));
        };
        if !self.array_var_stack.is_empty() {
            let var = self.array_var_stack.pop().unwrap();
            self.function_body.last_mut().unwrap().push_str(&format!("LIST_ALLOCATED({}, __list_ptr_new) = true;\nLIST_VAL({}, __list_ptr_new) = ", var, var));
        };
    }

    pub fn commit_for_loop(
        &mut self,
    ) {
        self.function_body.last_mut().unwrap().push_str("__list_ptr_new++;\n\
            __list_ptr++;\n\
            :: else -> __list_ptr++;\n\
            fi\n\
        od\n\
        }\n");
    }

    pub fn write_enum_random(
        &mut self,
        args: Vec<String>,
    ) {
        // TODO only pseudorandom as Promela does not support randomness
        let array = &args[0];
        let assignee = self.var_stack.last().unwrap().to_string();
        self.function_body.last_mut().unwrap().push_str(&format!("__list_random({}, {});\n", array, assignee));
        warn!("Random number generation is not supported in Promela");
    }

    pub fn write_enum_at(
        &mut self,
        args: Vec<String>,
    ) {
        let list = &args[0];
        let index = &args[1];
        self.function_body.last_mut().unwrap().push_str(&format!("__list_at({}, {})", list, index));
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
        self.function_channels.last_mut().unwrap().push_str(&format!("chan __anonymous_ret_{} = [1] of {{ int }};\n", self.anonymous_function_count));
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
}