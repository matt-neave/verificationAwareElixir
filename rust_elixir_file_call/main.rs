use std::process::Command;
use std::io::{Read, Write};
use std::fs::File;
use std::path::Path;

fn main() {
    let arg_error = "Incorrect usage: cargo run -- \"target_file\"";
    let arg_binding = std::env::args().nth(1).expect(arg_error);
    let dir = Path::new(&arg_binding);
    let out_file = "./ast_output.txt"; 
    let ast_extractor_code = &*format!("defmodule AstExtractor do
  def main do
    {{:ok, ast}} = Code.string_to_quoted(File.read!(\"{}\"))
    File.write!(\"ast_output.txt\", inspect(ast)) # Writing AST to a file
    ast
  end
end", dir.to_str().unwrap());

    let lib = "./lib";
    let extractor = &*format!("{}/ast_extactor.ex", lib);
    let ast_extractor = File::create(extractor);
    let _ = ast_extractor
        .expect("Failed to create AST extractor")
        .write_all(ast_extractor_code.as_bytes())
        .expect("Failed to write to AST extractor");

    let output = Command::new("mix")
        .args(&["run", "-e", "AstExtractor.main"])
        .output()
        .expect("Failed to execute Elixir script");

    if output.status.success() {
        let mut file = File::open(out_file).expect("Failed to open output file");
        let mut contents = String::new();
        file.read_to_string(&mut contents).expect("Failed to read output file");
        let _ = std::fs::remove_file(extractor);
        let _ = std::fs::remove_file(lib);
        println!("{}", contents);
    } else {
        println!("Error: {:?}", output.stderr);
    }
}