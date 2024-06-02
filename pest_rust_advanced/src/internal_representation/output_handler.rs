use std::fs::{File, OpenOptions};
use std::io::{self, BufRead, BufReader, Write};
use std::path::Path;

pub fn append_source_lines(model: &str, source: &str) -> io::Result<()> {
    // Open the model file for reading
    let model_path = Path::new(model);
    let model_file = File::open(&model_path)?;
    let model_reader = BufReader::new(model_file);

    // Open the source file for reading
    let source_path = Path::new(source);
    let source_file = File::open(&source_path)?;
    let source_reader = BufReader::new(source_file);

    // Read all lines from the source file into a vector
    let source_lines: Vec<String> = source_reader.lines().collect::<Result<_, _>>()?;

    // Open a temporary file to write the modified model contents
    let temp_model_path = model_path.with_extension("tmp");
    let mut temp_model_file = File::create(&temp_model_path)?;

    // Process each line in the model file
    for line in model_reader.lines() {
        let mut line = line?;
        // Find the placeholder pattern /*n*/
        if let Some(start) = line.find("/*") {
            if let Some(end) = line.find("*/") {
                if let Ok(line_number) = line[start + 2..end].trim().parse::<usize>() {
                    // Get the corresponding line from the source file
                    if line_number > 0 && line_number <= source_lines.len() {
                        let source_line = &source_lines[line_number - 1];
                        // Append the source line to the current line in the model
                        line.push_str(&format!("    /* {} */", source_line.trim()));
                    }
                }
            }
        }
        // Write the modified line to the temporary file
        writeln!(temp_model_file, "{}", line)?;
    }

    // Rename the temporary file to the original model file
    std::fs::rename(temp_model_path, model_path)?;

    Ok(())
}