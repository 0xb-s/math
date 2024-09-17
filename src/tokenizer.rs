// src/tokenizer.rs

use crate::token::Token;

pub fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = input.chars().collect();
    let mut idx = 0;

    while idx < chars.len() {
        let ch = chars[idx];

        match ch {
            ' ' | '\t' | '\n' => {
                idx += 1;
            }
            '+' => {
                tokens.push(Token::Plus);
                idx += 1;
            }
            '-' => {
                tokens.push(Token::Minus);
                idx += 1;
            }
            '*' => {
                tokens.push(Token::Star);
                idx += 1;
            }
            '/' => {
                tokens.push(Token::Slash);
                idx += 1;
            }
            '(' => {
                tokens.push(Token::LParen);
                idx += 1;
            }
            ')' => {
                tokens.push(Token::RParen);
                idx += 1;
            }
            '0'..='9' | '.' => {
                let mut num_str = String::new();
                while idx < chars.len() && (chars[idx].is_digit(10) || chars[idx] == '.') {
                    num_str.push(chars[idx]);
                    idx += 1;
                }
                let num = num_str.parse::<f64>().map_err(|e| e.to_string())?;
                tokens.push(Token::Number(num));
            }
            'a'..='z' | 'A'..='Z' => {
                let mut var_str = String::new();
                while idx < chars.len() && chars[idx].is_alphabetic() {
                    var_str.push(chars[idx]);
                    idx += 1;
                }
                tokens.push(Token::Variable(var_str));
            }
            _ => {
                return Err(format!("Unexpected character: '{}'", ch));
            }
        }
    }

    Ok(tokens)
}
