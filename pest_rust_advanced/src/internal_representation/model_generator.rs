use std::collections::HashMap;
use std::fs::File;
use std::io::{Read, Write};
use std::process::{Command, Stdio};
use regex::Regex;

use crate::internal_representation::model_runner::{SPIN_CMD, STATE_VEC_SIZE};

pub const PARAM_STR: &str = "__PARAM_VAR";

pub fn generate_models(model_path: &str) {
    println!("Generating models");

    // Open the file and read the contents to a string
    let mut file = File::open(model_path).expect("Could not open file");
    let mut contents = String::new();
    file.read_to_string(&mut contents).expect("Could not read file");

    // Count number of params
    let param_count: usize = contents.matches(PARAM_STR).count();

    // Each parameter will be bound between 0-2, a model is generated for all possible configurations
    let model_count = 2_usize.pow(param_count as u32);
    let mut model_params = HashMap::new();
    for i in 0..model_count {
        let mut model = contents.clone();
        let binary = format!("{:0width$b}", i, width = param_count);

        // Replace all occurrences of PARAM_STR with the corresponding binary value
        for c in binary.chars() {
            model = model.replacen(PARAM_STR, &c.to_string(), 1);
        }

        // Write the model to a file
        let model_name = format!("model_{}.pml", i);
        let mut model_file = File::create(model_name).expect("Could not create model file");
        model_params.insert(i, binary);
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
        let model_output;
        match stdout {
            Ok(s) => {
                model_output = s;
            }
            Err(e) => {
                panic!("Error: {}", e);
            }
        }

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
        std::fs::remove_file(model_name).expect("Could not delete model file");
    }

    let confidence = 1.0 - (violations as f64 / model_count as f64);
    println!("Acceptence confidence: {}.", confidence);

    if !violation_set.is_empty() {
        println!("Violations found in models:");
        for i in violation_set {
            println!("Model with params: {}", model_params.get(&i).unwrap());
        }
        println!("Assign these parameters to the system and re-run the verifier in verification mode to gather a trace");
    }
}