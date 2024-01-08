use std::io::{Read};
mod elixir_ast_repr;
pub use crate::elixir_ast_repr::parse_ast;

fn main() {

    let mut contents = String::new();
    let mut file = std::fs::File::open("./ast_output.txt").expect("Failed to open output file");
    file.read_to_string(&mut contents).expect("Failed to read output file");
    parse_ast(contents);
}
