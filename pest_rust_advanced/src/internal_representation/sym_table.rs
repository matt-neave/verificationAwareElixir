use std::collections::HashMap;

#[derive(Debug)]
pub enum SymbolType {
    Integer,
    String,
    Boolean,
}

pub struct SymbolEntry {
    name: String,
    symbol_type: SymbolType,
}

pub struct SymbolTable {
    pub entries: HashMap<String, SymbolType>,
}

impl SymbolTable {
    // Function to create a new symbol table
    pub fn new() -> Self {
        SymbolTable {
            entries: HashMap::new(),
        }
    }

    // Function to add a new entry to the symbol table
    pub fn add_entry(&mut self, name: String, symbol_type: SymbolType) {
        self.entries.insert(name, symbol_type);
    }

    // Unsafe
    // pub fn lookup(&self, name: &str) -> SymbolType {
    //     *self.entries.get(name).expect("Symbol not found")
    // }

    pub fn pretty_print(&self) {
        println!("Symbol Table:");
        for (name, symbol_type) in &self.entries {
            println!("{}: {:?}", name, symbol_type);
        }
    }
}
