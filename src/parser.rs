// src/parser.rs

use crate::ast::Expr;
use crate::token::Token;

pub struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens,
            position: 0,
        }
    }

    pub fn parse_expression(&mut self) -> Result<Expr, String> {
        self.parse_addition()
    }

    fn parse_addition(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_multiplication()?;

        while let Some(token) = self.current_token() {
            match token {
                Token::Plus => {
                    self.advance();
                    let rhs = self.parse_multiplication()?;
                    expr = Expr::Add(Box::new(expr), Box::new(rhs));
                }
                Token::Minus => {
                    self.advance();
                    let rhs = self.parse_multiplication()?;
                    expr = Expr::Sub(Box::new(expr), Box::new(rhs));
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    fn parse_multiplication(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_factor()?;

        loop {
            if let Some(token) = self.current_token() {
                match token {
                    Token::Star => {
                        self.advance();
                        let rhs = self.parse_factor()?;
                        expr = Expr::Mul(Box::new(expr), Box::new(rhs));
                    }
                    Token::Slash => {
                        self.advance();
                        let rhs = self.parse_factor()?;
                        expr = Expr::Div(Box::new(expr), Box::new(rhs));
                    }
                    // Handle implicit multiplication
                    Token::Number(_) | Token::Variable(_) | Token::LParen => {
                        let rhs = self.parse_factor()?;
                        expr = Expr::Mul(Box::new(expr), Box::new(rhs));
                    }
                    _ => break,
                }
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn parse_factor(&mut self) -> Result<Expr, String> {
        if let Some(token) = self.current_token() {
            match token {
                Token::Plus => {
                    self.advance();
                    self.parse_factor()
                }
                Token::Minus => {
                    self.advance();
                    let expr = self.parse_factor()?;
                    Ok(Expr::Mul(Box::new(Expr::Number(-1.0)), Box::new(expr)))
                }
                _ => self.parse_atom(),
            }
        } else {
            Err("Unexpected end of input".into())
        }
    }

    fn parse_atom(&mut self) -> Result<Expr, String> {
        if let Some(token) = self.current_token() {
            match token {
                Token::Number(n) => {
                    self.advance();
                    Ok(Expr::Number(n))
                }
                Token::Variable(name) => {
                    self.advance();
                    Ok(Expr::Variable(name))
                }
                Token::LParen => {
                    self.advance();
                    let expr = self.parse_expression()?;
                    if let Some(next_token) = self.current_token() {
                        if next_token == Token::RParen {
                            self.advance();
                            Ok(expr)
                        } else {
                            Err("Expected ')'".into())
                        }
                    } else {
                        Err("Expected ')'".into())
                    }
                }
                _ => Err(format!("Unexpected token: {:?}", token)),
            }
        } else {
            Err("Unexpected end of input".into())
        }
    }

    fn current_token(&self) -> Option<Token> {
        self.tokens.get(self.position).cloned()
    }

    fn advance(&mut self) {
        self.position += 1;
    }
}
