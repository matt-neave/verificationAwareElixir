// Runs spin, collects and triages information from the output

use std::process::{Command, Stdio};
use std::str::FromStr;
use regex::Regex;
use std::thread;
use std::sync::Arc;
use std::collections::HashMap;

pub const SPIN_CMD: &str = "spin";
pub const STATE_VEC_SIZE: &str = "409600";
const DEPTH_LIMIT: &str = "100000";
const FAIRNESS_LIMIT: &str = "100";
const _QUEUE_MEMORY: &str = "5000";
const _PROESS_MEMORY: &str = "500";
const _CHAN_MEMORY: &str = "500";
const VERBOSE: bool = false;
struct ErrorLine {
    process_num: u32,
    line_num: u32,
    valid_end_state: bool,
    function_name: String,
    start_of_cycle: bool,
    ltl_violation: bool,
    trail_ended: bool,
}

struct Message {
    process_num: u32,
    function_name: String,
    direction: String,
    data: String,
    mtype: String,
}

// Potential args
// if fair {
//     cmd.arg(&format!("-DVMAX={}", QUEUE_MEMORY));
//     cmd.arg(&format!("-DPMAX={}", PROESS_MEMORY));
//     cmd.arg(&format!("-DQMAX={}", CHAN_MEMORY));
// }

pub fn run_model(model_path: &str, elixir_dir: &str, fair: bool, reduce: bool, ltl_count: i32) {
    let mut cmds = HashMap::new();
    
    if ltl_count > 0 {
        for c in 1..=ltl_count {
            let dir = &format!("ltl_{}", c);
            let new_model_path = format!("{}/{}", dir, model_path);
            // Make a new directory for each model to copy the new model into
            let _ = std::fs::create_dir(format!("ltl_{}", c));
            std::fs::copy(model_path, &new_model_path).expect("Failed to copy model file.");
            let cmd = create_command(fair, reduce, Some(c), &model_path, dir);
            cmds.insert(new_model_path, cmd);
        }
    } else {
        let cmd = create_command(fair, reduce, None, model_path, ".");
        cmds.insert(String::from(model_path), cmd);
    }

    let elixir_dir = Arc::new(elixir_dir.to_owned());
    let total_runs = cmds.len() as i32;
    let mut error = false;
    println!("Running {} model(s).", total_runs);
    let start = std::time::Instant::now();
    
    let handles: Vec<_> = cmds.into_iter().map(|(path, mut cmd)| {
        println!("Running cmd: {:?}", cmd);
        let elixir_dir = Arc::clone(&elixir_dir);
    
        thread::spawn(move || {
            let output = cmd.output().expect("Failed to run model");
            (output, path, elixir_dir)
        })
    }).collect();
    
    // Process results sequentially
    for handle in handles {
        let (output, path, elixir_dir) = handle.join().expect("Failed to join thread");
        // Capture the output and print the result
        let stdout = String::from_utf8(output.stdout);
        error = match stdout {
            Ok(s) => {
                profile_errors(&path, &s, &elixir_dir)
            }
            Err(e) => {
                panic!("Error: {}", e)
            }
        };
    }
    
    if !error {
        println!("The verifier terminated with no errors.")
    }
    println!("Elapsed time: {:?}.", start.elapsed().as_secs_f64());

    if ltl_count > 0 {
        // for c in 1..=ltl_count {
        //     std::fs::remove_dir_all(format!("ltl_{}", c)).expect("Failed to remove directory.");
        // }
    }
}

fn create_command(fair: bool, reduce: bool, ltl_index: Option<i32>, model_path: &str, dir: &str) -> Command {
    let mut cmd = Command::new(SPIN_CMD);
    cmd
        .current_dir(dir)
        .arg("-search")
        .arg(&format!("-m{}", DEPTH_LIMIT));
    
    if fair {
        cmd.arg("-l")
            .arg("-f")
            .arg("-DNOREDUCE")
            .arg(&format!("-DNFAIR={}", FAIRNESS_LIMIT));
    }
    
    if reduce {
        cmd.arg("-DBITSTATE");
    }
    
    cmd.arg(&format!("-DVECTORSZ={}", STATE_VEC_SIZE));
    
    if let Some(index) = ltl_index {
        cmd
            .arg("-ltl")
            .arg(&format!("ltl_{}", index));
    }
    
    cmd.arg(model_path)
        .stdout(Stdio::piped());
    
    cmd
}

pub fn simulate_model(model_path: &str) {
    let _ = Command::new(SPIN_CMD)
        .arg(model_path)
        .stdout(Stdio::inherit())
        .output()
        .expect("Failed to run simulation");
}

fn profile_errors(model_path: &str, model_output: &str, elixir_dir: &str) -> bool {
    // Parse the output and determine errors    
    let re = Regex::new(r"errors: (\d+)").unwrap();

    if let Some(captures) = re.captures(model_output) {
        let number_str = &captures[1];
        
        if let Ok(error_count) = u32::from_str(number_str) {
            println!("Model ran successfully. {} error(s) found.", error_count);
            
            if error_count > 0 {
                check_invalid_end_state(model_path, model_output);

                check_non_accept_cycles(model_path, model_output);

                check_too_many_queues(model_path, model_output);

                check_assertion_violation(model_path, model_output);

                let (trace, messages) = generate_trace(model_path);

                report_elixir_trace(model_path, trace, messages, elixir_dir);
                true
            } else {
                false
            }
        } else {
            panic!("The model checker returned an unexpected output. \n{}", model_output);
        }
    } else {
        panic!("The model checker returned an unexpected output. \n{}", model_output);
    }
} 

fn check_invalid_end_state(model_path: &str, model_output: &str) {
    // Check if the model reached an invalid end state
    // If so, find the trace and report the errors to the user

    let match_str = "invalid end state (";

    if model_output.contains(match_str) {
        println!("The program likely reached a deadlock. Generating trace.");
    }
}

fn check_non_accept_cycles(model_path: &str, model_output: &str) {
    // Check for non acceptance cycles (livelock or ltl property not satisfied)
    let match_str = "acceptance cycle";

    if model_output.contains(match_str) {
        println!("The program is livelocked, or an ltl property was violated. Generating trace.");
    }
}

fn check_assertion_violation(model_path: &str, model_output: &str) {
    // Check for assertion violations
    let match_str = "assertion violated";

    if model_output.contains(match_str) {
        println!("An LTL, pre- or post-condition was violated. Generating trace.");
        let pattern = r"(?m)assertion violated.*$";
        let re = Regex::new(pattern).unwrap();
        if let Some(captures) = re.find(model_output) {
            let matched_portion = captures.as_str();
            println!("Violated: {}.", matched_portion);
        }
    }
}

fn check_too_many_queues(model_path: &str, model_output: &str) {
    // Check for too many queues
    let match_str = "too many queues";

    if model_output.contains(match_str) {
        println!("The execution depth implies a non-terminating path (a process is likely iterating unconditionally). Generating trace.");
    }
}

fn generate_trace(model_path: &str) -> (Vec<ErrorLine>, Vec<Message>) {
    // Run the trace
    let mut trace_output = Command::new("spin");

    let dir = model_path.split("/").collect::<Vec<&str>>();
    let path = dir[dir.len()-1];
    let dir_path = &dir[..dir.len()-1].join("/");
    let dir = if dir.len() == 1 { "." } else { dir_path };
    
    trace_output
        .current_dir(dir)
        .arg("-t") // View trace
        .arg("-r")
        .arg("-s");

    if VERBOSE {
        trace_output.arg("-v"); // Verbose trace if VERBOSE is true
    }

    let trace_output = trace_output
        .arg(path)
        .stdout(Stdio::piped())
        .output()
        .expect("Failed to get the trace.");

    let output_str = String::from_utf8(trace_output.stdout).expect("Failed to get the trace.");

    let re: Regex = Regex::new(r"\d+:\s*proc\s*(\d+)\s*\(([^)]+)\)\s*test_out\.pml:(\d+).*").unwrap();
    let re_message = Regex::new(r"\d+:\s*proc\s*(\d+)\s*\(([^):]+:[^)]*?)\)\s*test_out\.pml:\d+\s*(Send|Recv)\s*([^ ]+)\s*(->|<-)\s*queue\s*\d+\s*\(([^)]+)\)"
).unwrap();

    let mut trace = Vec::new();
    let mut messages = Vec::new();

    for line in output_str.lines() {
        if line.contains("START OF CYCLE") {
            let err = ErrorLine {
                process_num: 0,
                line_num: 0,
                valid_end_state: false,
                function_name: "".to_string(),
                start_of_cycle: true,
                ltl_violation: false,
                trail_ended: false,
            };
            trace.push(err);
        }

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
                start_of_cycle: false,
                ltl_violation: false,
                trail_ended: false,
            }; 
            trace.push(err);
        }

        if let Some(captures) = re_message.captures(line) {
            let process_number = captures.get(1).unwrap().as_str();
            let function_name = captures.get(2).unwrap().as_str();
            let message_data = captures.get(4).unwrap().as_str();
            let arrow_direction = captures.get(5).unwrap().as_str();
            let message_type = captures.get(6).unwrap().as_str();
        
            let message = Message {
                process_num: process_number.parse().unwrap(),
                function_name: function_name.to_string(),
                direction: arrow_direction.to_string(),
                data: message_data.to_string(),
                mtype: message_type.to_string(),
            };
            messages.push(message);
        }
    }
    (trace, messages)
}

fn report_elixir_trace(model_path: &str, trace: Vec<ErrorLine>, messages: Vec<Message>, elixir_dir: &str) {
    let model = std::fs::read_to_string(model_path).expect("Failed to read the model file.");
    let re: Regex = Regex::new(r"/\*(\d+)\*/").expect("Failed to compile regex");

    let elixir_file = std::fs::read_to_string(elixir_dir).expect("Failed to read the elixir file.");

    // First send all message events
    println!("<<<Message Events>>>");
    for (i, message) in messages.iter().enumerate() {
        println!(
            "[{}] ({}) {} [{}]",
            i+1,
            message.function_name,
            if message.direction == "<-" { "recv" } else { "send" },
            message.data.trim(),
        );
    }

    println!("\n<<<Error Trace>>>");
    // Then send the exact trace
    let mut eot = false;
    for (i, trace_line) in trace.iter().enumerate() {
        if trace_line.start_of_cycle {
            println!("<<< start of cycle >>>");
            continue;
        } else if trace_line.ltl_violation {
            println!("LTL PROPERTY VIOLATED");
            continue;
        } else if trace_line.trail_ended {
            println!("<<< END OF TRAIL, FINAL STATES: >>>");
            eot = true;
            continue;
        }

        let line = model.lines().nth((trace_line.line_num - 1) as usize).expect("Failed to get the line.");
        if let Some(captures) = re.captures(line) {
            let elixir_line_num: Result<u32, _> = captures[1].parse();
            if let Ok(x) = elixir_line_num {
                let mut elixir_line = "";
                if x > 0 {
                    elixir_line = elixir_file.lines().nth(x as usize).expect("Failed to get the line.");
                }
                if eot
                {
                    println!(
                        "[{}] (proc_{}) {}:{} [{}] {}", 
                        i+1,
                        trace_line.process_num, 
                        trace_line.function_name, 
                        x, 
                        elixir_line.trim(),
                        if trace_line.valid_end_state { "<status: TEMINATED>" } else { "<status: ALIVE>" },
                    );
                    continue;
                }
                println!(
                    "[{}] (proc_{}) {}:{} [{}]", 
                    i+1,
                    trace_line.process_num, 
                    trace_line.function_name, 
                    x, 
                    elixir_line.trim(),
                );
            }
        }
    }
}