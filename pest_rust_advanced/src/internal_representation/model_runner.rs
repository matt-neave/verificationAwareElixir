// Runs spin, collects and triages information from the output

use std::process::{Command, Stdio};
use std::str::FromStr;
use std::collections::HashMap;
use regex::Regex;

const SPIN_CMD: &str = "spin";
const MEM_LIMIT: &str = "40960";

pub fn run_model(model_path: &str) {
    let output = Command::new(SPIN_CMD)
        .arg("-search")
        .arg(&format!("-DVECTORSZ={}", MEM_LIMIT))
        .arg(model_path)
        .stdout(Stdio::piped())
        .output()
        .expect("Failed to run model");


    // Capture the output and print the result
    let stdout = String::from_utf8(output.stdout);
    match stdout {
        Ok(s) => {
            profile_errors(model_path,&s);
        }
        Err(e) => {
            panic!("Error: {}", e);
        }
    }
}

pub fn simulate_model(model_path: &str) {
    let _ = Command::new(SPIN_CMD)
        .arg(model_path)
        .stdout(Stdio::inherit())
        .output()
        .expect("Failed to run simulation");
}

fn profile_errors(model_path: &str, model_output: &str) {
    // Parse the output and determine errors    
    let re = Regex::new(r"errors: (\d+)").unwrap();

    if let Some(captures) = re.captures(model_output) {
        let number_str = &captures[1];
        
        if let Ok(error_count) = u32::from_str(number_str) {
            println!("Model checking ran successfully. {} error(s) found.", error_count);
            // println!("{}", model_output);

            if error_count > 0 {
                let mut trace_lines = HashMap::new();
                let invalid_end_state_lines = check_invalid_end_state(model_path, model_output);
                for (proc_num, line_num) in invalid_end_state_lines {
                    trace_lines.insert(proc_num, line_num);
                }

                report_elixir_trace(model_path, trace_lines);
            } else {
                println!("The verifier terminated with no errors.")
            }
        } else {
            panic!("The model checker returned an unexpected output.");
        }
    } else {
        panic!("The model checker returned an unexpected output.");
    }
} 

fn check_invalid_end_state(model_path: &str, model_output: &str) -> HashMap<u32, u32> {
    // Check if the model reached an invalid end state
    // If so, find the trace and report the errors to the user

    let match_str = "invalid end state";
    let mut process_to_line_map: HashMap<u32, u32> = HashMap::new();

    if model_output.contains(match_str) {
        println!("The program likely reached a deadlock. Generating trace.");
        // Run the trace
        let trace_output = Command::new("spin")
            .arg("-t")
            .arg(model_path)
            .stdout(Stdio::piped())
            .output()
            .expect("Failed to get the trace.");

        let output_str = String::from_utf8(trace_output.stdout).expect("Failed to get the trace.");


        let re = Regex::new(r"\d+:\s*proc\s*(\d+).*test_out\.pml:(\d+)").unwrap();

        for line in output_str.lines() {
            if let Some(captures) = re.captures(line) {
                let proc_number: u32 = captures[1].parse().expect("Failed to get trace (process number).");
                let line_number: u32 = captures[2].parse().expect("Failed to get trace (line number).");
                process_to_line_map.insert(proc_number, line_number);
            }
        }
    }
    process_to_line_map
}

fn report_elixir_trace(model_path: &str, trace_lines: HashMap<u32, u32>) {
    let model = std::fs::read_to_string(model_path).expect("Failed to read the model file.");
    let re = Regex::new(r"/\*(\d+)\*/").expect("Failed to compile regex");

    for (proc_num, line_num) in &trace_lines {
        let line = model.lines().nth((line_num - 1) as usize).expect("Failed to get the line.");
        if let Some(captures) = re.captures(line) {
            let elixir_line_num: Result<u32, _> = captures[1].parse();
            if let Ok(x) = elixir_line_num {
                println!("(proc_{}) stuck on line: {}.", proc_num, x);
            }
        }
    }
}