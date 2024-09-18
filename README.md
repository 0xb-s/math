# Symbolic Math Calculation Library

This library provides tools for parsing, tokenizing, simplifying, and formatting symbolic mathematical expressions. It allows you to handle symbolic math expressions, such as simplifying algebraic equations, generating tokens from expressions, and more.

## Features

- **Tokenization**: Converts a string expression into tokens.
- **Parsing**: Parses tokens into an expression tree.
- **Simplification**: Simplifies symbolic mathematical expressions.
- **Formatting**: Formats expressions into readable strings.


### Example Usage

Here is a simple example demonstrating how to use the library to parse and simplify a symbolic mathematical expression.



```rust
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
```


### Running the Example

You can run the example using the following command:

```bash
cargo run --example foo
```
```bash
cargo run --example bar
``` 
