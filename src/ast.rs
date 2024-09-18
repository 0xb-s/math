// src/ast.rs
use std::fmt;
use std::ops::Div;
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Number(f64),
    Variable(String),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Pow(Box<Expr>, Box<Expr>),
    Undefined,
}

impl Div for Expr {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Expr::Mul(ll, lr), Expr::Mul(rl, rr)) if *ll == *rl => Expr::Div(lr, rr),

            (l, r) => Expr::Div(Box::new(l), Box::new(r)),
        }
    }
}
impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Number(n) => {
                if n.fract() == 0.0 {
                    write!(f, "{}", n.round())
                } else {
                    write!(f, "{}", n)
                }
            }
            Expr::Variable(var) => write!(f, "{}", var),
            Expr::Add(lhs, rhs) => write!(f, "({} + {})", lhs, rhs),
            Expr::Sub(lhs, rhs) => write!(f, "({} - {})", lhs, rhs),
            Expr::Mul(lhs, rhs) => write!(f, "({} * {})", lhs, rhs),
            Expr::Div(lhs, rhs) => write!(f, "({} / {})", lhs, rhs),
            Expr::Undefined => write!(f, "undefined"),
            Expr::Pow(_, _) => todo!(),
        }
    }
}
