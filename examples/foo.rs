use math::format::format_expr;
use math::parser::Parser;
use math::simplify::simplify;
use math::tokenizer::tokenize;

fn main() {
    let expr_str = "(2x + x) * 2 * 2";
    match tokenize(expr_str) {
        Ok(tokens) => {
            println!("Tokens: {:?}", tokens);
            let mut parser = Parser::new(tokens);
            match parser.parse_expression() {
                Ok(expr) => {
                    println!("Parsed expression: {:?}", expr);
                    let simplified_expr = simplify(expr);
                    println!("Simplified expression: {}", format_expr(&simplified_expr));
                }
                Err(e) => {
                    println!("Error parsing expression: {}", e);
                }
            }
        }
        Err(e) => {
            println!("Error tokenizing input: {}", e);
        }
    }
}
