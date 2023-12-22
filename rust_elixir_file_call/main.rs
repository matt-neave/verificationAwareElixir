use std::process::Command;
use std::io::{Write, Read};

fn main() {
    let output = Command::new("mix")
        .args(&["run", "-e", "AstExtractor.main"])
        .current_dir("./basic_deadlock")
        .output()
        .expect("Failed to execute Elixir script");

    if output.status.success() {
        let mut file = std::fs::File::open("./basic_deadlock/ast_output.txt").expect("Failed to open output file");
        let mut contents = String::new();
        file.read_to_string(&mut contents).expect("Failed to read output file");
        println!("Elixir output: {}", contents);
    } else {
        println!("Error: {:?}", output.stderr);
    }
}
