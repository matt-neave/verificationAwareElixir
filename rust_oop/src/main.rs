struct BinaryExpression {
    operator: String,
    left: i32,
    right: i32,
}

impl BinaryExpression {
    fn apply(&self) -> i32 { 
        match self.operator.as_str() {
            "add" => self.left + self.right,
            "subtract" => self.left - self.right,
            _ => {
                println!("This is not a valid operator");
                println!("Moving on!");
                0
            },
        }
    }
}

fn main() {
    let new_expr = BinaryExpression {
        operator: String::from("fart"),
        left: 5,
        right: 2
    };

    println!("Operator is {}", new_expr.operator);

    println!("Evaluated expression is {}", new_expr.apply());
}

