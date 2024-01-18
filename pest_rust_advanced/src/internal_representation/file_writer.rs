use std::fs::File;
use std::io::{self, Write};
use std::collections::HashMap;

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
        self.content.push_str(format!("{}\n", text).as_str());
    }

    pub fn new_function(&mut self, func_name: &str, arguments: Option<&str>) {
        // TODO: look into using annotation instead of matching on start
        match &*func_name {
            "start" => self.content.push_str(&*format!("init {{\n")),
            _       => self.content.push_str(&*format!("proctype {} {{\n", &*func_name)),
        }
    }

    pub fn commit_function(&mut self) {
        // Commits the current function to the file
        self.content.push_str(&*format!("{}\n", &*self.function_metabody));
        self.content.push_str(&*format!("{}}}\n\n", &*self.function_body));
        self.function_metabody = String::new();
        self.function_body = String::new();
        self.function_call_count = 0;
    }

    pub fn write_function_call(&mut self, func_name: &str, call_arguments: &str, return_variable: &str) {
        // Track how many function calls have taken place 
        // Create a channel for each
        // Name the receive variables appropriately
        // TODO determine return type    
        self.function_call_count += 1;
        self.function_metabody.push_str(&*format!("chan ret{} = [1] of {{ int }};\n", self.function_call_count));
        
        // TODO make a mapping of variable name
        let call_arguments = call_arguments.replace("[", "(");
        let call_arguments = call_arguments.replace("]", ")");
        self.function_body.push_str(&*format!("run {}{});\n", func_name, call_arguments));
        self.function_body.push_str(&*format!("int {};\n", return_variable));
        self.function_body.push_str(&*format!("ret{} ? {}\n", self.function_call_count, return_variable)); 
    }

    // Method to commit the content to the file and reset the string
    pub fn commit(&mut self) -> io::Result<()> {
        self.file.write_all(self.content.as_bytes())?;
        self.content.clear(); // Reset the string
        Ok(())
    }
}