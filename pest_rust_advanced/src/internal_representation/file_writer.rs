use std::fs::File;
use std::collections::HashMap;

use std::io::{self, Write};

use crate::formatted_condition;
use crate::internal_representation::sym_table;

// Todo: bodies should be stack based to handle nesting
pub struct FileWriter {
    _header: String,
    content: String,
    function_body: String,
    function_channels: String,
    function_metabody: String,
    function_call_count: u32,
    process_count: i32,
    mailbox_id: HashMap<String, i32>,
    process_name: HashMap<i32, String>,
    var_stack: Vec<String>,
    mtype: Vec<String>,
    _maximum_message_size: u32,
    function_messages: u32,
    receive_count: u32,
    file: File,
}

impl FileWriter {
    // Constructor method to create a new instance
    pub fn new(file_path: &str) -> io::Result<Self> {
        let file = File::create(file_path)?;
        Ok(Self {
            _header: String::new(),
            content: String::new(),
            function_body: String::new(),
            function_channels: String::new(),
            function_metabody: String::new(),
            function_call_count: 0,
            process_count: 0,
            mailbox_id: HashMap::new(),
            process_name: HashMap::new(),
            var_stack: Vec::new(),
            mtype: Vec::new(),
            _maximum_message_size: 1,
            function_messages: 0,
            receive_count: 0,
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
            sym_table::SymbolType::Boolean => String::from("int")
        }
    }

    fn format_arguments(arguments: &str, sym_table: sym_table::SymbolTable) -> String {
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


    pub fn new_function(&mut self, func_name: &str, arguments: &str, sym_table: sym_table::SymbolTable, init: bool) {
        if init {
            self.content.push_str("init {\n");
            self.function_channels.push_str("chan p0_mailbox = [10] of { mtype, MessageList };\n");
            self.function_body.push_str("mailbox[0] = p0_mailbox;\n");
            self.function_body.push_str("int __pid = 0;\n");
        } else if arguments.is_empty() {
            self.content.push_str(&format!("proctype {} (chan ret; int __pid) {{\n", func_name));
        } else {
            let formatted_args = Self::format_arguments(arguments, sym_table);
            self.content.push_str(&format!("proctype {} ({}; chan ret; int __pid) {{\n", func_name, &*formatted_args));
        }
    }

    pub fn commit_function(&mut self) {
        // Commits the current function to the file
        self.content.push_str(&self.function_channels);
        self.content.push_str(&self.function_metabody);
        self.content.push_str(&format!("{}}}\n\n", &*self.function_body));
        self.function_channels = String::new();
        self.function_metabody = String::new();
        self.function_body = String::new();
        self.function_call_count = 0;
        self.function_messages = 0;
    }

    pub fn write_function_call(&mut self, func_name: &str, call_arguments: &str, return_variable: &str, _ret: bool /* TODO */) {
        // Track how many function calls have taken place 
        // Create a channel for each
        // Name the receive variables appropriately
        // TODO determine return type    
        self.function_call_count += 1;
        self.function_channels.push_str(&format!("chan ret{} = [1] of {{ int }};\n", self.function_call_count));
        
        // TODO make a mapping of variable name
        let call_arguments = call_arguments.replace('[', "(");
        let call_arguments = call_arguments.replace(']', "");
        let mut return_variable = return_variable.to_owned();
        if return_variable.is_empty() {
           return_variable = format!("val{}", self.function_call_count); 
        }
        self.function_body.push_str(&format!("run {}{}, ret{}, __pid);\n", func_name, call_arguments, self.function_call_count));
        self.function_body.push_str(&format!("int {};\n", return_variable));
        self.function_body.push_str(&format!("ret{} ? {}\n", self.function_call_count, return_variable)); 
    }

    fn condition_to_string(expr: &formatted_condition::FormattedCondition) -> String {
        let mut symbol_map = HashMap::new();
        symbol_map.insert("or", "||");
        symbol_map.insert("and", "&&");   
        symbol_map.insert(">=", ">="); 
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

        // Write header meta information
        // TODO: paramatise mailbox length and byte array lengths
        // TODO: use maximum_message_size to determine number of messages in list
        let unique_mtypes = self.mtype.iter().cloned().collect::<std::collections::HashSet<String>>().iter().cloned().collect::<Vec<String>>();
        let mut var_name = String::new();
        if !unique_mtypes.is_empty() {
            var_name = String::from(&format!("mtype = {{{}}};\n", unique_mtypes.join(",")));
        }
        var_name.push_str(&format!("typedef MessageType {{\nbyte data1[20];\nint data2;\nbyte data3[20];\nbool data4;\n}};\ntypedef\nMessageList {{\nMessageType m1;\nMessageType m2;\nMessageType m3;\n}};\nchan mailbox[{}] = [10] of {{ mtype, MessageList }};\n\n", self.process_count + 1));
        let header_buf = var_name
            .as_bytes();

        let _ = self.file.write_all(header_buf);

        // Write parsed content
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

    pub fn write_assignment_variable(&mut self, var: &str) {
        self.function_body.push_str(&format!("int {};\n", var));
        self.function_body.push_str(&format!("{} = ", var));

        // Push the variable name to the stack to be applied by spawn
        self.var_stack.push(String::from(var));
    }

    pub fn write_spawn_process(&mut self, proctype: &str, args: &str) {
        self.process_count += 1;
        self.function_call_count += 1;
        self.function_channels.push_str(&format!("chan ret{} = [1] of {{ int }};\n", self.function_call_count));

        // Format args depending on if they are empty
        let formatted_args = format!("{}{}ret{},{}", args, if args.is_empty() {""} else {","}, self.function_call_count, self.function_call_count);

        let var_name = self.var_stack.pop();
        let i = self.process_count;
        if let Some(x) = var_name {
            // Create a mailbox for each process
            self.function_channels.push_str(&format!("chan p{}_mailbox = [10] of {{ mtype, MessageList }};\n", self.process_count));            
            self.function_metabody.push_str(&format!("mailbox[{}] = p{}_mailbox;\n", i, i));
            self.function_body.push_str(&format!("run {}({});\n", proctype, formatted_args));

            // Add to the lookup tables
            self.process_name.insert(i, x.clone());
            self.mailbox_id.insert(x.clone(), i);
        } else {
            panic!("Missing variable name in process stack");
        }
    }

    pub fn write_send(&mut self, target: &str, mut args: Vec<String>) {
        let mailbox: i32 = *self.mailbox_id.get(target).unwrap_or(&-1);
        let mtype = args.remove(0).replace(':', "").to_uppercase();
        self.mtype.push(mtype.clone());

        // Create the message component
        let mut i = 1;
        self.function_body.push_str(&format!("MessageList msg_{};\n", self.function_messages));
        for mut arg in args {
            // TODO: replace third argument with type
            if arg.starts_with("{:self,") {
                arg = String::from("__pid");
            }

            self.function_body.push_str(&format!("msg_{}.m{}.data{} = {};\n", self.function_messages, i, 2, arg));
            i += 1;
        }
        if mailbox == -1 {
            self.function_body.push_str(&format!("mailbox[{}] ! {}, msg_{};\n", target, mtype, self.function_messages));
        } else {
            self.function_body.push_str(&format!("mailbox[{}] ! {}, msg_{};\n", mailbox, mtype, self.function_messages));
        }
        self.function_messages += 1;
    }

    pub fn write_receive(&mut self) {
        self.function_body.push_str("do\n:: true ->\n");
        self.function_body.push_str("mtype messageType;\n");
        self.function_body.push_str(&format!("MessageList rec_v_{};\n", self.receive_count));
        self.function_body.push_str(&format!("mailbox[__pid] ? messageType, rec_v_{};\nif\n", self.receive_count));
        self.receive_count += 1;
    }

    pub fn commit_receive(&mut self) {
        self.function_body.push_str(&format!(":: else -> mailbox[_pid] ! messageType, rec_v_{};\n", self.receive_count - 1));
        self.function_body.push_str("fi;\nod;\n");
    }

    pub fn write_receive_assignment(&mut self, assignments: Vec<String>) {
        // First element is the message type
        for (i, assignment) in assignments.iter().enumerate() {
            if i == 0 {
                self.mtype.push(assignment.to_uppercase());
                self.function_body.push_str(&format!(":: messageType == {} ->\n", assignment.to_uppercase()));
            } else {
                self.function_body.push_str(&format!("int {};\n", assignment));
                self.function_body.push_str(&format!("{} = rec_v_{}.m{}.{}\n", assignment, self.receive_count - 1, i, "data2"));
            }
        }
    }
    
    pub fn write_end_receive_statement(&mut self) {
        self.function_body.push_str("break;\n");
    }

    pub fn write_io(&mut self, io_put: &str) {
        self.function_body.push_str(&format!("printf(\"{}\\n\");\n", io_put));
    }

    pub fn start_unless(&mut self) {
        self.function_body.push_str("{\n")
    }

    pub fn write_unless_condition(
        &mut self,
        condition: formatted_condition::FormattedCondition
    ) {
        self.function_body.push_str("}\nunless\n{");
        self.function_body.push_str(format!("{}\n", Self::condition_to_string(&condition)).as_str());
        self.function_body.push_str("}\n")
    }
}