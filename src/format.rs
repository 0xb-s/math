// src/format.rs

use crate::ast::Expr;

pub fn format_expr(expr: &Expr) -> String {
    match expr {
        Expr::Number(n) => {
            if n.fract() == 0.0 {
                format!("{}", n.round())
            } else {
                format!("{}", n)
            }
        }
        Expr::Variable(var) => var.clone(),
        Expr::Add(lhs, rhs) => {
            format!("{} + {}", format_expr(lhs), format_expr(rhs))
        }
        Expr::Sub(lhs, rhs) => {
            format!("{} - {}", format_expr(lhs), format_expr(rhs))
        }
        Expr::Mul(lhs, rhs) => {
            let left = format_factor(lhs);
            let right = format_factor(rhs);
            format!("{}{}", left, right)
        }
        Expr::Div(lhs, rhs) => {
            format!("({})/({})", format_expr(lhs), format_expr(rhs))
        }
    }
}

fn format_factor(expr: &Expr) -> String {
    match expr {
        Expr::Add(_, _) | Expr::Sub(_, _) => {
            format!("({})", format_expr(expr))
        }
        _ => format_expr(expr),
    }
}
