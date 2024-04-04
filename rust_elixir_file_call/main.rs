use std::process::Command;
use std::io::{Read, Write};
use std::fs::File;

fn main() {
    let arg_error = "Incorrect usage: cargo run -- \"source_dir\"";
    let ast_extractor_code = "defmodule AstExtractor do
    def main do
      IO.puts(\"Main called\")
      {:ok, ast} = Code.string_to_quoted(File.read!(\"./lib/basic_sequential.ex\"))
      File.write!(\"ast_output.txt\", inspect(ast)) # Writing AST to a file
      ast
      end
    end";

    let dir = std::env::args().nth(1).expect(arg_error);
    let extractor = &*format!("{}/ast_extactor.ex", dir.clone());
    let ast_extractor = File::create(extractor);
    let _ = ast_extractor
        .expect("Failed to create AST extractor")
        .write_all(ast_extractor_code.as_bytes())
        .expect("Failed to write to AST extractor");

    let output = Command::new("mix")
        .args(&["run", "-e", "AstExtractor.main"])
        .current_dir(dir.clone())
        .output()
        .expect("Failed to execute Elixir script");

    if output.status.success() {
        let mut file = File::open(format!("{}/ast_output.txt", dir)).expect("Failed to open output file");
        let mut contents = String::new();
        file.read_to_string(&mut contents).expect("Failed to read output file");
        let _ = std::fs::remove_file(extractor);
        println!("{}", contents);
    } else {
        println!("Error: {:?}", output.stderr);
    }
}
