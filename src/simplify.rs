// src/simplify.rs

use crate::ast::Expr;
use crate::solver::Solver;
use std::collections::HashMap;
/// Type alias for variable exponents.
/// Uses `i32` to represent integer exponents.
pub type VarExponents = HashMap<String, i32>;
/// Builds an expression from a map of variables to their exponents.
/// Positive exponents are placed in the numerator, negative in the denominator.
fn build_expr_from_var_map(var_map: &VarExponents) -> Expr {
    let mut numerator_terms = Vec::new();
    let mut denominator_terms = Vec::new();

    for (var, exp) in var_map {
        if *exp > 0 {
            for _ in 0..*exp {
                numerator_terms.push(Expr::Variable(var.clone()));
            }
        } else if *exp < 0 {
            for _ in 0..(-*exp) {
                denominator_terms.push(Expr::Variable(var.clone()));
            }
        }
    }

    // Build numerator expression
    let numerator = if numerator_terms.is_empty() {
        Expr::Number(1.0)
    } else {
        let mut expr = numerator_terms.remove(0);
        for term in &numerator_terms {
            expr = Expr::Mul(Box::new(expr), Box::new(term.clone()));
        }
        expr
    };

    // Build denominator expression
    let denominator = if denominator_terms.is_empty() {
        Expr::Number(1.0)
    } else {
        let mut expr = denominator_terms.remove(0);
        for term in &denominator_terms {
            expr = Expr::Mul(Box::new(expr), Box::new(term.clone()));
        }
        expr
    };

    // Construct the final expression
    if denominator_terms.is_empty() && numerator_terms.is_empty() && numerator == Expr::Number(1.0)
    {
        Expr::Number(1.0)
    } else if denominator_terms.is_empty() {
        numerator
    } else if numerator == Expr::Number(1.0) {
        denominator
    } else {
        Expr::Div(Box::new(numerator), Box::new(denominator))
    }
}

/// Simplifies a given mathematical expression by expanding, collecting like terms,
/// and reducing coefficients iteratively until no further simplifications can be made.
pub fn simplify(expr: Expr) -> Expr {
    let mut current = expr;
    let max_iterations = 100; // Prevent infinite loops TODO change this
    let mut iterations = 0;

    while iterations < max_iterations {
        let expanded = expand_expr(&current);
        let collected = collect_like_terms(&expanded);

        if collected == current {
            break;
        }

        current = collected;
        iterations += 1;
    }

    current
}

/// Expands the expression by applying distributive laws where applicable.
fn expand_expr(expr: &Expr) -> Expr {
    match expr {
        Expr::Add(lhs, rhs) => Expr::Add(Box::new(expand_expr(lhs)), Box::new(expand_expr(rhs))),
        Expr::Pow(base, exponent) => {
            let expanded_base = expand_expr(base);
            let expanded_exponent = expand_expr(exponent);
            Expr::Pow(Box::new(expanded_base), Box::new(expanded_exponent))
        }
        Expr::Sub(lhs, rhs) => Expr::Sub(Box::new(expand_expr(lhs)), Box::new(expand_expr(rhs))),
        Expr::Mul(lhs, rhs) => {
            let left = expand_expr(lhs);
            let right = expand_expr(rhs);
            match (&left, &right) {
                // Distribute multiplication over addition: a * (b + c) = a*b + a*c
                (Expr::Add(a, b), c) => {
                    let left_mul = Expr::Mul(a.clone(), Box::new(c.clone()));
                    let right_mul = Expr::Mul(b.clone(), Box::new(c.clone()));
                    Expr::Add(
                        Box::new(expand_expr(&left_mul)),
                        Box::new(expand_expr(&right_mul)),
                    )
                }
                // Distribute multiplication over subtraction: a * (b - c) = a*b - a*c
                (Expr::Sub(a, b), c) => {
                    let left_mul = Expr::Mul(a.clone(), Box::new(c.clone()));
                    let right_mul = Expr::Mul(b.clone(), Box::new(c.clone()));
                    Expr::Sub(
                        Box::new(expand_expr(&left_mul)),
                        Box::new(expand_expr(&right_mul)),
                    )
                }
                (a, Expr::Add(b, c)) => {
                    let left_mul = Expr::Mul(Box::new(a.clone()), b.clone());
                    let right_mul = Expr::Mul(Box::new(a.clone()), c.clone());
                    Expr::Add(
                        Box::new(expand_expr(&left_mul)),
                        Box::new(expand_expr(&right_mul)),
                    )
                }
                (a, Expr::Sub(b, c)) => {
                    let left_mul = Expr::Mul(Box::new(a.clone()), b.clone());
                    let right_mul = Expr::Mul(Box::new(a.clone()), c.clone());
                    Expr::Sub(
                        Box::new(expand_expr(&left_mul)),
                        Box::new(expand_expr(&right_mul)),
                    )
                }

                _ => Expr::Mul(Box::new(left), Box::new(right)),
            }
        }
        // Expr::Div(lhs, rhs) => {
        //     match **lhs {
        //         // Distribute division over addition and subtraction
        //         Expr::Add(ref left, ref right) => Expr::Add(
        //             Box::new(Expr::Div(
        //                 Box::new(expand_expr(left)),
        //                 Box::new(expand_expr(rhs).clone()),
        //             )),
        //             Box::new(Expr::Div(
        //                 Box::new(expand_expr(right)),
        //                 Box::new(expand_expr(rhs).clone()),
        //             )),
        //         ),
        //         Expr::Sub(ref left, ref right) => Expr::Sub(
        //             Box::new(Expr::Div(
        //                 Box::new(expand_expr(left)),
        //                 Box::new(expand_expr(rhs).clone()),
        //             )),
        //             Box::new(Expr::Div(
        //                 Box::new(expand_expr(right)),
        //                 Box::new(expand_expr(rhs).clone()),
        //             )),
        //         ),
        //         // For multiplication and other operations, proceed as before
        //         _ => Expr::Div(Box::new(expand_expr(lhs)), Box::new(expand_expr(rhs))),
        //     }
        // }
        Expr::Div(lhs, rhs) => {
            // Ensure the expansion covers the distribution over multiplication
            let left_expanded = expand_expr(lhs);
            let right_expanded = expand_expr(rhs);
            match (left_expanded, right_expanded) {
                //  handle divisions where both sides involve multiplication
                (Expr::Mul(l_lhs, l_rhs), Expr::Mul(r_lhs, r_rhs)) => {
                    // Compare and simplify directly if variables and coefficients allow
                    // TODO make this make
                    if l_lhs == r_lhs {
                        Expr::Div(l_rhs, r_rhs)
                    } else if l_rhs == r_rhs {
                        Expr::Div(l_lhs, r_lhs)
                    } else {
                        // Default back to division if not directly simplifiable
                        // better way TODO
                        Expr::Div(
                            Box::new(Expr::Mul(l_lhs, l_rhs)),
                            Box::new(Expr::Mul(r_lhs, r_rhs)),
                        )
                    }
                }
                // Default division expansion
                (l, r) => Expr::Div(Box::new(l), Box::new(r)),
            }
        }
        // Expr::Div(lhs, rhs) => Expr::Div(Box::new(expand_expr(lhs)), Box::new(expand_expr(rhs))),
        _ => expr.clone(),
    }
}

/// Collects like terms in the expression and combines their coefficients.
/// This version now cancels common terms in division.
fn collect_like_terms(expr: &Expr) -> Expr {
    let mut terms_map: HashMap<String, f64> = HashMap::new();
    collect_terms(expr, &mut terms_map, 1.0, &mut HashMap::new());

    // Check for undefined expressions
    if terms_map.contains_key("Undefined") {
        return Expr::Undefined;
    }

    // Separate positive and negative terms
    let mut positive_terms = Vec::new();
    let mut negative_terms = Vec::new();

    for (var_key, coeff) in terms_map {
        if coeff == 0.0 {
            continue;
        }
        if coeff > 0.0 {
            positive_terms.push((var_key, coeff));
        } else {
            negative_terms.push((var_key, -coeff)); 
        }
    }

    // Build the expression
    let mut exprs = Vec::new();

    // Add positive terms
    for (var_key, coeff) in positive_terms {
        let term_expr = if var_key.is_empty() {
            Expr::Number(coeff)
        } else {
            // Parse the variable key back into variables and exponents
            let factors = var_key.split('*').filter(|s| !s.is_empty());
            let mut expr_term: Option<Expr> = None;

            for factor in factors {
                let parts: Vec<&str> = factor.split('^').collect();
                let var = parts[0].to_string();
                let exp: i32 = parts.get(1).and_then(|e| e.parse().ok()).unwrap_or(1);

                let var_expr = Expr::Variable(var.clone());
                let powered_var = if exp == 1 {
                    var_expr
                } else {
                 
                    let mut expr_power = Expr::Variable(var.clone());
                    for _ in 1..exp {
                        expr_power =
                            Expr::Mul(Box::new(expr_power), Box::new(Expr::Variable(var.clone())));
                    }
                    expr_power
                };

                expr_term = Some(match expr_term {
                    None => powered_var,
                    Some(existing) => Expr::Mul(Box::new(existing), Box::new(powered_var)),
                });
            }

         
            if coeff == 1.0 {
                expr_term.unwrap()
            } else {
                Expr::Mul(Box::new(Expr::Number(coeff)), Box::new(expr_term.unwrap()))
            }
        };
        exprs.push(term_expr);
    }

    // Start with the first positive term or zero
    let mut result = if let Some(first) = exprs.pop() {
        first
    } else {
        Expr::Number(0.0)
    };

    // Add remaining positive terms
    for term in exprs {
        result = Expr::Add(Box::new(result), Box::new(term));
    }

    // Subtract negative terms
    for (var_key, coeff) in negative_terms {
        let term_expr = if var_key.is_empty() {
            Expr::Number(coeff)
        } else {
            // Parse the variable key back into variables and exponents
            let factors = var_key.split('*').filter(|s| !s.is_empty());
            let mut expr_term: Option<Expr> = None;

            for factor in factors {
                let parts: Vec<&str> = factor.split('^').collect();
                let var = parts[0].to_string();
                let exp: i32 = parts.get(1).and_then(|e| e.parse().ok()).unwrap_or(1);

                let var_expr = Expr::Variable(var.clone());
                let powered_var = if exp == 1 {
                    var_expr
                } else {
                    // Handle exponents by repeated multiplication
                    let mut expr_power = Expr::Variable(var.clone());
                    for _ in 1..exp {
                        expr_power =
                            Expr::Mul(Box::new(expr_power), Box::new(Expr::Variable(var.clone())));
                    }
                    expr_power
                };

                expr_term = Some(match expr_term {
                    None => powered_var,
                    Some(existing) => Expr::Mul(Box::new(existing), Box::new(powered_var)),
                });
            }

          
            if coeff == 1.0 {
                expr_term.unwrap()
            } else {
                Expr::Mul(Box::new(Expr::Number(coeff)), Box::new(expr_term.unwrap()))
            }
        };

        result = Expr::Sub(Box::new(result), Box::new(term_expr));
    }

    // Further simplify the combined expression
    reduce_coefficients(result)
}

/// Parses a serialized variable key into a `VarExponents` map.
/// Example: "x^2*y^-1" -> {"x": 2, "y": -1}
fn parse_var_key(var_key: &str) -> VarExponents {
    let mut var_map = HashMap::new();
    if var_key.is_empty() {
        return var_map;
    }
    for factor in var_key.split('*') {
        let parts: Vec<&str> = factor.split('^').collect();
        let var = parts[0].to_string();
        let exp: i32 = parts.get(1).and_then(|e| e.parse().ok()).unwrap_or(1);
        *var_map.entry(var).or_insert(0) += exp;
    }
    var_map
}

/// Recursively collects terms from the expression and populates the `terms` map.
/// - `expr`: The current expression to process.
/// - `terms`: A map from variable keys to their coefficients.
/// - `coeff`: The current coefficient multiplier.
/// - `current_vars`: The current mapping of variables to their exponents.
fn collect_terms(
    expr: &Expr,
    terms: &mut HashMap<String, f64>,
    coeff: f64,
    _current_vars: &mut VarExponents, // todo: use this in future
) {
    match expr {
        Expr::Pow(base, exponent) => {
            if let Expr::Number(exp) = **exponent {
                if exp.fract() != 0.0 || exp < 0.0 {
                    *terms.entry("Undefined".to_string()).or_insert(0.0) +=
                        coeff * std::f64::INFINITY;
                    return;
                }

                let exp_u32 = exp as u32;
                let mut base_vars = VarExponents::new();
                // Use `traverse_expr_vars` instead of `traverse_expr`
                if let Err(_) = Solver::traverse_expr_vars(base, 1.0, &mut base_vars) {
                    *terms.entry("Undefined".to_string()).or_insert(0.0) +=
                        coeff * std::f64::INFINITY;
                    return;
                }

                if base_vars.len() != 1 {
                    *terms.entry("Undefined".to_string()).or_insert(0.0) +=
                        coeff * std::f64::INFINITY;
                    return;
                }

                let (var, var_exp) = base_vars.iter().next().unwrap();
                let new_exp = var_exp * exp_u32 as i32;
                let var_key = format!("{}^{}", var, new_exp);

                *terms.entry(var_key).or_insert(0.0) += coeff;
            } else {
                *terms.entry("Undefined".to_string()).or_insert(0.0) += coeff * std::f64::INFINITY;
            }
        }
        Expr::Add(lhs, rhs) => {
            collect_terms(lhs, terms, coeff, _current_vars);
            collect_terms(rhs, terms, coeff, _current_vars);
        }
        Expr::Sub(lhs, rhs) => {
            collect_terms(lhs, terms, coeff, _current_vars);
            collect_terms(rhs, terms, -coeff, _current_vars);
        }
        Expr::Mul(lhs, rhs) => {
            let (lhs_coeff, lhs_vars) = extract_coeff_and_vars(lhs, 1.0);
            let (rhs_coeff, rhs_vars) = extract_coeff_and_vars(rhs, 1.0);
            let total_coeff = coeff * lhs_coeff * rhs_coeff;

            // Merge exponents
            let mut merged_vars = lhs_vars.clone();
            for (var, exp) in rhs_vars.iter() {
                *merged_vars.entry(var.clone()).or_insert(0) += exp;
            }

            let var_key = serialize_vars(&merged_vars);
            *terms.entry(var_key).or_insert(0.0) += total_coeff;
        }
        Expr::Div(lhs, rhs) => {
            // Extract numerator coefficients and variables
            let (numerator_coeff, numerator_vars) = extract_coeff_and_vars(lhs, 1.0);
            // Extract denominator coefficients and variables
            let (denominator_coeff, denominator_vars) = extract_coeff_and_vars(rhs, 1.0);

            // Prevent division by zero
            if denominator_coeff == 0.0 {
                // Represent division by zero as undefined
                *terms.entry("Undefined".to_string()).or_insert(0.0) += coeff * std::f64::INFINITY;
                return;
            }

            // Compute the total coefficient
            let total_coeff = coeff * numerator_coeff / denominator_coeff;

            // Adjust variables: numerator_vars - denominator_vars
            let mut adjusted_vars = numerator_vars.clone();
            for (var, exp) in denominator_vars.iter() {
                *adjusted_vars.entry(var.clone()).or_insert(0) -= exp;
            }

            let var_key = serialize_vars(&adjusted_vars);
            *terms.entry(var_key).or_insert(0.0) += total_coeff;
        }
        Expr::Number(n) => {
            *terms.entry(String::new()).or_insert(0.0) += coeff * n;
        }
        Expr::Variable(var) => {
            let mut vars = HashMap::new();
            *vars.entry(var.clone()).or_insert(0) += 1;
            let var_key = serialize_vars(&vars);
            *terms.entry(var_key).or_insert(0.0) += coeff;
        }
        Expr::Undefined => {
            // Represent undefined expressions
            *terms.entry("Undefined".to_string()).or_insert(0.0) += coeff * std::f64::INFINITY;
        }
    }
}

/// Extracts the coefficient and variables from an expression.
/// Returns a tuple containing the coefficient and a map of variables to their exponents.
fn extract_coeff_and_vars(expr: &Expr, current_coeff: f64) -> (f64, VarExponents) {
    let mut coeff = current_coeff;
    let mut vars = HashMap::new();

    match expr {
        Expr::Number(n) => {
            coeff *= n;
        }
        Expr::Variable(var) => {
            *vars.entry(var.clone()).or_insert(0) += 1;
        }
        Expr::Mul(lhs, rhs) => {
            let (lhs_coeff, mut lhs_vars) = extract_coeff_and_vars(lhs, 1.0);
            let (rhs_coeff, mut rhs_vars) = extract_coeff_and_vars(rhs, 1.0);
            coeff *= lhs_coeff * rhs_coeff;

            // Merge exponents
            for (var, exp) in rhs_vars.drain() {
                *lhs_vars.entry(var.clone()).or_insert(0) += exp;
            }

            vars = lhs_vars;
        }
        Expr::Div(lhs, rhs) => {
            let (lhs_coeff, lhs_vars) = extract_coeff_and_vars(lhs, 1.0);
            let (rhs_coeff, rhs_vars) = extract_coeff_and_vars(rhs, 1.0);

            if rhs_coeff == 0.0 {
                // Represent division by zero as undefined
                coeff *= std::f64::INFINITY;
            } else {
                coeff *= lhs_coeff / rhs_coeff;

                // Adjust exponents: lhs_vars - rhs_vars
                for (var, exp) in rhs_vars.iter() {
                    *vars.entry(var.clone()).or_insert(0) -= exp;
                }
            }
        }
        Expr::Undefined => {
            // Represent undefined expressions
            coeff *= std::f64::INFINITY;
        }
        _ => {}
    }

    (coeff, vars)
}

/// Serializes the variables and their exponents into a sorted, canonical string key.
/// Example: {"x": 2, "y": 1} -> "x^2*y"
fn serialize_vars(vars: &VarExponents) -> String {
    let mut serialized = Vec::new();
    let mut sorted_vars: Vec<_> = vars.iter().collect();
    sorted_vars.sort_by(|a, b| a.0.cmp(b.0));

    for (var, exp) in sorted_vars {
        if *exp != 0 {
            if *exp == 1 {
                serialized.push(var.clone());
            } else {
                serialized.push(format!("{}^{}", var, exp));
            }
        }
    }

    serialized.join("*")
}

/// Reduces coefficients in the expression by combining numerical terms.
fn reduce_coefficients(expr: Expr) -> Expr {
    match expr {
        Expr::Add(lhs, rhs) => {
            let left = reduce_coefficients(*lhs);
            let right = reduce_coefficients(*rhs);
            match (left.clone(), right.clone()) {
                (Expr::Number(a), Expr::Number(b)) => Expr::Number(a + b),
                (Expr::Number(a), _) if a == 0.0 => right,
                (_, Expr::Number(b)) if b == 0.0 => left,
                (Expr::Undefined, _) | (_, Expr::Undefined) => Expr::Undefined,
                (a, b) => Expr::Add(Box::new(a), Box::new(b)),
            }
        }
        Expr::Sub(lhs, rhs) => {
            let left = reduce_coefficients(*lhs);
            let right = reduce_coefficients(*rhs);
            match (left, right.clone()) {
                (Expr::Number(a), Expr::Number(b)) => Expr::Number(a - b),
                (a, Expr::Number(b)) if b == 0.0 => a,
                (Expr::Number(a), _) if a == 0.0 => {
                    Expr::Sub(Box::new(Expr::Number(0.0)), Box::new(right))
                }
                (Expr::Undefined, _) | (_, Expr::Undefined) => Expr::Undefined,
                (a, b) => Expr::Sub(Box::new(a), Box::new(b)),
            }
        }
        Expr::Mul(lhs, rhs) => {
            let left = reduce_coefficients(*lhs);
            let right = reduce_coefficients(*rhs);
            match (left, right) {
                (Expr::Number(a), Expr::Number(b)) => Expr::Number(a * b),
                (Expr::Number(0.0), _) | (_, Expr::Number(0.0)) => Expr::Number(0.0),
                (Expr::Number(1.0), b) => b,
                (a, Expr::Number(1.0)) => a,
                (Expr::Undefined, _) | (_, Expr::Undefined) => Expr::Undefined,
                (a, b) => Expr::Mul(Box::new(a), Box::new(b)),
            }
        }
        Expr::Pow(base, exponent) => {
            let reduced_base = reduce_coefficients(*base);
            let reduced_exponent = reduce_coefficients(*exponent);
            match (reduced_base, reduced_exponent) {
                (Expr::Number(b), Expr::Number(e)) if e.fract() == 0.0 => Expr::Number(b.powf(e)),
                (Expr::Undefined, _) | (_, Expr::Undefined) => Expr::Undefined,
                (b, e) => Expr::Pow(Box::new(b), Box::new(e)),
            }
        }
        Expr::Div(lhs, rhs) => {
            let left = reduce_coefficients(*lhs);
            let right = reduce_coefficients(*rhs);
            match (left.clone(), right.clone()) {
                (Expr::Number(a), Expr::Number(b)) if b != 0.0 => Expr::Number(a / b),
                (Expr::Number(_), Expr::Number(b)) if b == 0.0 => Expr::Undefined,
                (Expr::Mul(ll, lr), Expr::Mul(rl, rr)) if ll == rl => *lr / *rr,
                (Expr::Mul(ll, lr), Expr::Mul(rl, rr)) if lr == rr => *ll / *rl,
                (l, Expr::Number(r)) if r != 0.0 => {
                    Expr::Mul(Box::new(l), Box::new(Expr::Number(1.0 / r)))
                }

                (a, Expr::Number(1.0)) => a,
                (Expr::Undefined, _) | (_, Expr::Undefined) => Expr::Undefined,
                (a, b) => Expr::Div(Box::new(a), Box::new(b)),
                _ => Expr::Div(Box::new(left), Box::new(right)),
            }
        }
        Expr::Undefined => Expr::Undefined,
        _ => expr,
    }
}
