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

    // Method to commit the content to the file and reset the string
    pub fn commit(&mut self) -> io::Result<()> {
        self.file.write_all(self.content.as_bytes())?;
        self.content.clear(); // Reset the string
        Ok(())
    }
}