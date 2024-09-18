use math::solver::solve_equation;

fn main() {
    let equations = vec![
        "2x + 3 = 7",
        "x/0 = 5",
        "x^2 - 4 = 0",
        "x^3 - 1 = 0",
        "5 = 5",
        "3 = 7",
        "x^4 + 1 = 0",
    ];

    for equation_str in equations {
        println!("\nSolving Equation: {}", equation_str);
        match solve_equation(equation_str) {
            Ok(solution) => println!("Solution: {}", solution),
            Err(e) => println!("Error: {}", e),
        }
    }
}
