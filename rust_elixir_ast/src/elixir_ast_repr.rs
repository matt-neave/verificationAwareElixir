fn split_arguments(input: &str) -> Vec<String> {
    let mut arguments = Vec::new();
    let mut current_argument = String::new();
    let mut nesting_level = 0;

    for c in input.chars() {
        match c {
            '{' => {
                nesting_level += 1;
                if nesting_level > 1 {
                    current_argument.push(c);
                }
            }
            '}' => {
                nesting_level -= 1;
                if nesting_level > 0 {
                    current_argument.push(c);
                } else {
                    arguments.push(current_argument.clone());
                    current_argument.clear();
                }
            }
            ',' => {
                if nesting_level == 0 {
                    arguments.push(current_argument.clone());
                    current_argument.clear();
                } else {
                    current_argument.push(c);
                }
            }
            _ => current_argument.push(c),
        }
    }

    if !current_argument.is_empty() {
        arguments.push(current_argument);
    }

    arguments
}

pub fn parse_ast(contents: String) {
    let arguments = split_arguments(&contents);

    for argument in arguments {
        println!("{}", argument);
    }
}
