// src/simplify.rs

use crate::ast::Expr;
use std::collections::HashMap;

pub fn simplify(expr: Expr) -> Expr {
    let expanded_expr = expand_expr(&expr);
    collect_like_terms(&expanded_expr)
}

fn expand_expr(expr: &Expr) -> Expr {
    match expr {
        Expr::Add(lhs, rhs) => {
            let left = expand_expr(lhs);
            let right = expand_expr(rhs);
            Expr::Add(Box::new(left), Box::new(right))
        }
        Expr::Sub(lhs, rhs) => {
            let left = expand_expr(lhs);
            let right = expand_expr(rhs);
            Expr::Sub(Box::new(left), Box::new(right))
        }
        Expr::Mul(lhs, rhs) => {
            let left = expand_expr(lhs);
            let right = expand_expr(rhs);
            match (left, right) {
                // Distribute multiplication over addition
                (Expr::Add(a, b), c) => {
                    let left_mul = expand_expr(&Expr::Mul(a, Box::new(c.clone())));
                    let right_mul = expand_expr(&Expr::Mul(b, Box::new(c)));
                    Expr::Add(Box::new(left_mul), Box::new(right_mul))
                }
                (a, Expr::Add(b, c)) => {
                    let left_mul = expand_expr(&Expr::Mul(Box::new(a.clone()), b));
                    let right_mul = expand_expr(&Expr::Mul(Box::new(a), c));
                    Expr::Add(Box::new(left_mul), Box::new(right_mul))
                }
                (a, b) => Expr::Mul(Box::new(a), Box::new(b)),
            }
        }
        _ => expr.clone(),
    }
}
fn collect_like_terms(expr: &Expr) -> Expr {
    let mut terms = HashMap::new();
    collect_terms(expr, &mut terms, 1.0);

    // Build the simplified expression from collected terms
    let mut exprs = vec![];

    for (var, coeff) in terms {
        if coeff == 0.0 {
            continue;
        }
        let term = if var.is_empty() {
            Expr::Number(coeff)
        } else if coeff == 1.0 {
            Expr::Variable(var)
        } else {
            Expr::Mul(Box::new(Expr::Number(coeff)), Box::new(Expr::Variable(var)))
        };
        exprs.push(term);
    }

    // Combine terms into a single expression
    if exprs.is_empty() {
        Expr::Number(0.0)
    } else {
        let mut result = exprs.remove(0);
        for e in exprs {
            result = Expr::Add(Box::new(result), Box::new(e));
        }
        result
    }
}

fn collect_terms(expr: &Expr, terms: &mut HashMap<String, f64>, coeff: f64) {
    match expr {
        Expr::Add(lhs, rhs) => {
            collect_terms(lhs, terms, coeff);
            collect_terms(rhs, terms, coeff);
        }
        Expr::Sub(lhs, rhs) => {
            collect_terms(lhs, terms, coeff);
            collect_terms(rhs, terms, -coeff);
        }
        Expr::Mul(lhs, rhs) => {
            let mut new_coeff = coeff;
            let mut vars = Vec::new();
            collect_factors(lhs, &mut new_coeff, &mut vars);
            collect_factors(rhs, &mut new_coeff, &mut vars);
            vars.sort(); // Ensure consistent ordering
            let var_key = vars.join("*");
            *terms.entry(var_key).or_insert(0.0) += new_coeff;
        }
        Expr::Number(n) => {
            *terms.entry(String::new()).or_insert(0.0) += coeff * n;
        }
        Expr::Variable(var) => {
            *terms.entry(var.clone()).or_insert(0.0) += coeff;
        }
        _ => {}
    }
}

fn collect_factors(expr: &Expr, coeff: &mut f64, vars: &mut Vec<String>) {
    match expr {
        Expr::Number(n) => {
            *coeff *= *n;
        }
        Expr::Variable(var) => {
            vars.push(var.clone());
        }
        Expr::Mul(lhs, rhs) => {
            collect_factors(lhs, coeff, vars);
            collect_factors(rhs, coeff, vars);
        }
        _ => {}
    }
}
