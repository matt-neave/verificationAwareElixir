// Runs spin, collects and triages information from the output

use std::process::{Command, Stdio};
use std::str::FromStr;
use regex::Regex;

const SPIN_CMD: &str = "spin";
const MEM_LIMIT: &str = "409600";
const DEPTH_LIMIT: &str = "100000";
const FAIRNESS_LIMIT: &str = "100";
const QUEUE_MEMORY: &str = "5000";
const PROESS_MEMORY: &str = "500";
const CHAN_MEMORY: &str = "500";

struct ErrorLine {
    process_num: u32,
    line_num: u32,
    valid_end_state: bool,
    function_name: String,
}

pub fn run_model(model_path: &str) {
    let output = Command::new(SPIN_CMD)
        .arg("-search")
        .arg(&format!("-m{}", DEPTH_LIMIT))
        .arg(&format!("-DVECTORSZ={}", MEM_LIMIT))
        .arg(&format!("-DNFAIR{}", FAIRNESS_LIMIT))
        .arg(&format!("-DVMAX{}", QUEUE_MEMORY))
        .arg(&format!("-DPMAX{}", PROESS_MEMORY))
        .arg(&format!("-DQMAX{}", CHAN_MEMORY))
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
                let mut trace_lines = Vec::new();
                let invalid_end_state_lines = check_invalid_end_state(model_path, model_output);
                for trace in invalid_end_state_lines {
                    trace_lines.push(trace);
                }

                let non_accept_cycles = check_non_accept_cycles(model_path, model_output);
                for trace in non_accept_cycles {
                    trace_lines.push(trace);
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

fn check_invalid_end_state(model_path: &str, model_output: &str) -> Vec<ErrorLine> {
    // Check if the model reached an invalid end state
    // If so, find the trace and report the errors to the user

    let match_str = "invalid end state (";
    let mut trace = Vec::new();

    if model_output.contains(match_str) {
        println!("The program likely reached a deadlock. Generating trace.");
        trace = generate_trace(model_path);
    }
    trace
}

fn check_non_accept_cycles(model_path: &str, model_output: &str) -> Vec<ErrorLine> {
    // Check for non acceptance cycles (livelock or ltl property not satisfied)
    let match_str = "acceptance cycle";
    let mut trace = Vec::new();

    if model_output.contains(match_str) {
        println!("The program is livelocked, or an ltl property was violated. Generating trace.");
        trace = generate_trace(model_path);
    }
    trace
}

fn generate_trace(model_path: &str) -> Vec<ErrorLine> {
    // Run the trace
    let trace_output = Command::new("spin")
        .arg("-t")
        .arg(model_path)
        .stdout(Stdio::piped())
        .output()
        .expect("Failed to get the trace.");

    let output_str = String::from_utf8(trace_output.stdout).expect("Failed to get the trace.");

    if output_str.contains("START OF CYCLE") {
        println!("Start of cycle:")
    }

    let re = Regex::new(r"\d+:\s*proc\s*(\d+)\s*\(([^)]+)\)\s*test_out\.pml:(\d+).*").unwrap();
    let mut trace = Vec::new();
    for line in output_str.lines() {
        if let Some(captures) = re.captures(line) {
            let proc_number: u32 = captures[1].parse().unwrap_or(0);
            let function_name = captures[2].to_string().chars()
                .filter(|c| c.is_alphabetic() || *c == '_')
                .collect();
            let line_number: u32 = captures[3].parse().unwrap_or(0);
            let valid = line.contains("valid end state");
            let err = ErrorLine {
                process_num: proc_number,
                line_num: line_number,
                valid_end_state: valid,
                function_name,
            }; 
            trace.push(err);
        }
    }
    trace
}

fn report_elixir_trace(model_path: &str, trace: Vec<ErrorLine>) {
    let model = std::fs::read_to_string(model_path).expect("Failed to read the model file.");
    let re = Regex::new(r"/\*(\d+)\*/").expect("Failed to compile regex");

    for trace_line in trace {
        let line = model.lines().nth((trace_line.line_num - 1) as usize).expect("Failed to get the line.");
        if let Some(captures) = re.captures(line) {
            let elixir_line_num: Result<u32, _> = captures[1].parse();
            if let Ok(x) = elixir_line_num {
                println!(
                    "(proc_{}) {}:{} <{} state>", 
                    trace_line.process_num, 
                    trace_line.function_name, 
                    x, 
                    if trace_line.valid_end_state { "Valid" } else { "Invalid" }
                );
            }
        }
    }
}