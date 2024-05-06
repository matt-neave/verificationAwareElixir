use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum SymbolType {
    Integer,
    String,
    Boolean,
    NoRet,  // Special type for non returning function
    Array(Box<SymbolType>, i32),
    Unknown,
}

impl PartialEq for SymbolType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (SymbolType::Integer, SymbolType::Integer)
            | (SymbolType::String, SymbolType::String)
            | (SymbolType::Boolean, SymbolType::Boolean)
            | (SymbolType::Unknown, SymbolType::Unknown) => true,
            (SymbolType::Array(inner_type1, _), SymbolType::Array(inner_type2, _)) => {
                inner_type1 == inner_type2
            }
            _ => false,
        }
    }
}

pub struct SymbolTable {
    pub entries: HashMap<String, SymbolType>,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
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

    pub fn remove_entry(&mut self, name: &str) {
        self.entries.remove(name);
    }

    pub fn replace_entry(&mut self, name: &str, symbol_type: SymbolType) {
        self.entries.insert(name.to_string(), symbol_type);
    }

    // Unsafe
    pub fn lookup(&self, name: &str) -> &SymbolType {
        self.entries.get(name).unwrap_or_else(|| panic!("missing symbol: {}", name))
    }

    pub fn safe_lookup(&self, name: &str) -> Option<&SymbolType> {
        self.entries.get(name)
    }

    pub fn update_array_size(&mut self, name: &str, size: i32) {
        let symbol_type = self.lookup(name);
        match symbol_type {
            SymbolType::Array(inner_type, _) => {
                self.replace_entry(name, SymbolType::Array((*inner_type).clone(), size));
            }
            _ => panic!("Tried to update size of non-array type"),
        }
    }

    pub fn pretty_print(&mut self) {
        println!("Symbol Table:");
        for (name, symbol_type) in &self.entries {
            println!("{}: {:?}", name, symbol_type);
        }
    }

    pub fn get_return_type(&mut self) -> &SymbolType {
        // Edge case to get return type
        let ret_v = "RET_V";
        if self.entries.contains_key(ret_v) {
            self.lookup(ret_v)
        } else {
            &SymbolType::Unknown
        }
    }

    pub fn contains(&mut self, name: &str) -> bool {
        self.entries.contains_key(name)
    }
}

pub fn get_array_inner_type(symbol_type: &SymbolType) -> &SymbolType {
    match symbol_type {
        SymbolType::Array(inner_type, _) => inner_type,
        _ => panic!("Tried to get inner type of non-array type"),
    }
}

pub fn get_array_size(symbol_type: &SymbolType) -> i32 {
    match symbol_type {
        SymbolType::Array(_, size) => *size,
        _ => panic!("Tried to get size of non-array type"),
    }
}