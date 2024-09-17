#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Number(f64),
    Variable(String),
    Plus,
    Minus,
    Star,
    Slash,
    LParen,
    RParen,
}
