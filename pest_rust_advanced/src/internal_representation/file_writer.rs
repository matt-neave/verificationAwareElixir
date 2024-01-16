use std::fs::File;
use std::io::{self, Write};

pub struct FileWriter {
    content: String,
    file: File,
}

impl FileWriter {
    // Constructor method to create a new instance
    pub fn new(file_path: &str) -> io::Result<Self> {
        let file = File::create(file_path)?;
        Ok(Self {
            content: String::new(),
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

    pub fn write_function_call(&mut self, func_name: &str, call_arguments: &str) {
        // Track how many function calls have taken place 
        // Create a channel for each
        // Name the receive variables appropriately
        self.content.push_str(format!("{}({})\n", func_name, call_arguments).as_str());
    }

    // Method to commit the content to the file and reset the string
    pub fn commit(&mut self) -> io::Result<()> {
        self.file.write_all(self.content.as_bytes())?;
        self.content.clear(); // Reset the string
        Ok(())
    }
}