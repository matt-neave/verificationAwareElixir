use std::collections::HashMap;
use std::collections::BTreeMap;
use std::fs::File;
use std::io::{Read, Write};
use std::process::{Command, Stdio};
use regex::Regex;

use crate::internal_representation::model_runner::{SPIN_CMD, STATE_VEC_SIZE};

pub const PARAM_STR: &str = "__PARAM_VAR";

fn generate_configs(n: usize, p: usize) -> Vec<String> {
    let mut sequence = Vec::new();
    // Create a sequence of n^p values, each string is p characters and ranges from 0 to n-1
    // i.e. for n=2, p=3, the sequence will be ["000", "001", "010", "011", "100", "101", "110", "111"]
    // for n=3, p=2, the sequence will be ["00", "01", "02", "10", "11", "12", "20", "21", "22"]
    for i in 0..n.pow(p as u32) {
        let mut config = String::new();
        let mut j = i;
        for _ in 0..p {
            let digit = j % n;
            config.push_str(&digit.to_string());
            j /= n;
        }
        sequence.push(config.chars().rev().collect::<String>());
    }
    sequence
}

pub fn generate_models(model_path: &str, params: Vec<String>, n: u32) {
    println!("Generating models.");

    // Open the file and read the contents to a string
    let mut file = File::open(model_path).expect("Could not open file");
    let mut contents = String::new();
    file.read_to_string(&mut contents).expect("Could not read file");

    // Count number of params
    let param_count: usize = contents.matches(PARAM_STR).count();
    let model_count = (n as usize).pow(param_count as u32);
    let mut model_params = HashMap::new();
    let configs = generate_configs(n as usize, param_count);
    for (i, config) in configs.iter().enumerate() {
        let mut model = contents.clone();

        // Replace all occurrences of PARAM_STR with the corresponding binary value
        for c in config.chars() {
            model = model.replacen(PARAM_STR, &c.to_string(), 1);
        }

        // Write the model to a file
        let model_name = format!("model_{}.pml", i);
        let mut model_file = File::create(model_name).expect("Could not create model file");
        model_params.insert(i, config);
        model_file.write_all(model.as_bytes()).expect("Could not write to model file");
    }
    println!("Generated {} models.", model_count);

    let mut violations = 0;
    let mut violation_set = Vec::new();
    for i in 0..model_count {
        println!("Verifying model {} of {}.", i + 1, model_count);
        let model_name = format!("model_{}.pml", i);
        let output = Command::new(SPIN_CMD)
            .arg("-search")
            .arg(&format!("-DVECTORSZ={}", STATE_VEC_SIZE))
            .arg(model_name)
            .stdout(Stdio::piped())
            .output()
            .expect("Failed to run model");
        let stdout = String::from_utf8(output.stdout);
        let model_output = match stdout {
            Ok(s) => {
                s
            }
            Err(e) => {
                panic!("Error: {}", e);
            }
        };

        let re = Regex::new(r"errors: (\d+)").unwrap();

        if let Some(captures) = re.captures(&model_output) {
            let number_str = &captures[1];
            if number_str.parse::<i32>().unwrap() > 0 {
                violations += 1;
                violation_set.push(i);
            }
        }
    }

    // Delete all the models
    for i in 0..model_count {
        let model_name = format!("model_{}.pml", i);
        let model_name_trail = format!("model_{}.pml.trail", i);
        let _ = std::fs::remove_file(model_name);
        let _ = std::fs::remove_file(model_name_trail);
    }

    let confidence = 1.0 - (violations as f64 / model_count as f64);
    println!("Acceptance confidence: {}.", confidence);

    if !violation_set.is_empty() {
        println!("Violations found in models:");
        for i in violation_set {
            // Zip params with model_params
            let violation_params = model_params.get(&i).unwrap();
            let violated_map = params.iter().zip(violation_params.chars()).collect::<BTreeMap<_, _>>();
            println!("Model with params: {:?}", violated_map);
        }
        println!("Assign these parameters to the system and re-run the verifier in verification mode to gather a trace.");
    }
}