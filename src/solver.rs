// src/solver.rs

use crate::ast::Expr;
use crate::format::format_expr;
use crate::parser::Parser;
use crate::simplify::simplify;
use crate::simplify::VarExponents;
use crate::tokenizer::tokenize;
use std::collections::HashMap;
use std::fmt;
/// Represents a mathematical equation with left-hand side (lhs) and right-hand side (rhs).
#[derive(Debug, Clone, PartialEq)]
pub struct Equation {
    pub lhs: Expr,
    pub rhs: Expr,
}

impl Equation {
    /// Creates a new Equation.
    pub fn new(lhs: Expr, rhs: Expr) -> Self {
        Equation { lhs, rhs }
    }
}

impl fmt::Display for Equation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.lhs, self.rhs)
    }
}

/// Represents the solution to an equation.
#[derive(Debug, Clone, PartialEq)]
pub enum Solution {
    NoSolution,
    InfiniteSolutions,
    SingleSolution(f64),
    MultipleSolutions(Vec<f64>),
    Undefined,
}

impl fmt::Display for Solution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Solution::NoSolution => write!(f, "No solution"),
            Solution::InfiniteSolutions => write!(f, "Infinite solutions"),
            Solution::SingleSolution(val) => write!(f, "x = {}", val),
            Solution::MultipleSolutions(vals) => {
                write!(f, "Solutions: {:?}", vals)
            }
            Solution::Undefined => write!(f, "Undefined"),
        }
    }
}

/// Represents a polynomial with coefficients mapped to their corresponding exponents.
#[derive(Debug, Clone, PartialEq)]
pub struct Polynomial {
    /// Maps exponents to their coefficients.
    /// Example: {0: 2.0, 1: -3.0, 2: 1.0} represents 1x² - 3x + 2
    pub terms: HashMap<u32, f64>,
}

impl Polynomial {
    /// Creates a new, empty Polynomial.
    pub fn new() -> Self {
        Polynomial {
            terms: HashMap::new(),
        }
    }

    /// Adds a term to the polynomial.
    pub fn add_term(&mut self, exponent: u32, coefficient: f64) {
        *self.terms.entry(exponent).or_insert(0.0) += coefficient;
        // Remove the term if the coefficient becomes zero
        if let Some(coeff) = self.terms.get(&exponent) {
            if *coeff == 0.0 {
                self.terms.remove(&exponent);
            }
        }
    }

    /// Retrieves the coefficient for a given exponent.
    pub fn get_coefficient(&self, exponent: u32) -> f64 {
        *self.terms.get(&exponent).unwrap_or(&0.0)
    }

    /// Determines the degree of the polynomial.
    pub fn degree(&self) -> u32 {
        self.terms.keys().cloned().max().unwrap_or(0)
    }

    /// Normalizes the polynomial by removing zero coefficients.
    pub fn normalize(&mut self) {
        self.terms.retain(|_, &mut coeff| coeff != 0.0);
    }
}

/// Errors that can occur during polynomial parsing and solving.
#[derive(Debug, Clone)]
pub enum SolverError {
    InvalidEquation,
    NonPolynomial,
    UnsupportedDegree(u32),
    DivisionByZero,
    Undefined,
    ParsingError(String),
}

impl fmt::Display for SolverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolverError::InvalidEquation => write!(f, "Invalid equation format."),
            SolverError::NonPolynomial => write!(f, "The equation is not a polynomial."),
            SolverError::UnsupportedDegree(degree) => {
                write!(f, "Unsupported polynomial degree: {}", degree)
            }
            SolverError::DivisionByZero => write!(f, "Division by zero encountered."),
            SolverError::Undefined => write!(f, "The equation is undefined."),
            SolverError::ParsingError(msg) => write!(f, "Parsing error: {}", msg),
        }
    }
}

impl std::error::Error for SolverError {}

/// Represents the type of polynomial equation.
#[derive(Debug, Clone, PartialEq)]
pub enum PolynomialType {
    Linear,    // Degree 1
    Quadratic, // Degree 2
    Cubic,     // Degree 3
}

/// Main Solver struct employing the Builder Pattern.
pub struct Solver {
    equation: Equation,
}

impl Solver {
    /// Creates a new Solver with the given Equation.
    pub fn builder() -> SolverBuilder {
        SolverBuilder::new()
    }

    /// Solves the equation and returns the solution.
    pub fn solve(&self) -> Result<Solution, SolverError> {
        // Step 1: Parse the equation into a Polynomial (lhs - rhs = 0)
        let mut polynomial = Self::parse_equation(&self.equation)?;

        // Step 2: Normalize the polynomial
        polynomial.normalize();

        // Step 3: Determine the degree
        let degree = polynomial.degree();

        // Step 4: Solve based on degree
        match degree {
            0 => {
                // Constant equation: c = 0
                let c = polynomial.get_coefficient(0);
                if c == 0.0 {
                    Ok(Solution::InfiniteSolutions)
                } else {
                    Ok(Solution::NoSolution)
                }
            }
            1 => {
                // Linear equation: ax + b = 0
                Self::solve_linear(&polynomial)
            }
            2 => {
                // Quadratic equation: ax² + bx + c = 0
                Self::solve_quadratic(&polynomial)
            }
            3 => {
                // Cubic equation: ax³ + bx² + cx + d = 0
                Self::solve_cubic(&polynomial)
            }
            _ => Err(SolverError::UnsupportedDegree(degree)),
        }
    }

    /// Parses the Equation into a Polynomial by subtracting rhs from lhs.
    fn parse_equation(equation: &Equation) -> Result<Polynomial, SolverError> {
        let mut polynomial = Polynomial::new();

        // Parse lhs and add terms
        let lhs_terms = Self::collect_terms(&equation.lhs)?;
        for (exp, coeff) in lhs_terms {
            polynomial.add_term(exp, coeff);
        }

        // Parse rhs and subtract terms
        let rhs_terms = Self::collect_terms(&equation.rhs)?;
        for (exp, coeff) in rhs_terms {
            polynomial.add_term(exp, -coeff);
        }

        // Normalize the polynomial
        polynomial.normalize();

        Ok(polynomial)
    }

    /// Collects terms from an Expr and returns a HashMap of exponents to coefficients.
    fn collect_terms(expr: &Expr) -> Result<HashMap<u32, f64>, SolverError> {
        let mut terms: HashMap<u32, f64> = HashMap::new();
        Self::traverse_expr(expr, 1.0, &mut terms)?;
        Ok(terms) // Return `terms` of type `HashMap<u32, f64>`
    }

    pub fn traverse_expr(
        expr: &Expr,
        multiplier: f64,
        terms: &mut HashMap<u32, f64>,
    ) -> Result<(), SolverError> {
        match expr {
            Expr::Pow(base, exponent) => {
                // Ensure the exponent is a number
                if let Expr::Number(exp) = **exponent {
                    if exp.fract() != 0.0 || exp < 0.0 {
                        return Err(SolverError::NonPolynomial);
                    }

                    let exp_u32 = exp as u32;

                    // Traverse the base expression with the updated multiplier
                    let mut base_terms = HashMap::new();
                    Self::traverse_expr(base, multiplier, &mut base_terms)?;

                    // Multiply the exponents by exp_u32
                    for (existing_exp, coeff) in base_terms {
                        let new_exp = existing_exp * exp_u32;
                        *terms.entry(new_exp).or_insert(0.0) += coeff;
                    }
                } else {
                    return Err(SolverError::NonPolynomial);
                }
            }
            Expr::Add(lhs, rhs) => {
                Self::traverse_expr(lhs, multiplier, terms)?;
                Self::traverse_expr(rhs, multiplier, terms)?;
            }
            Expr::Sub(lhs, rhs) => {
                Self::traverse_expr(lhs, multiplier, terms)?;
                Self::traverse_expr(rhs, -multiplier, terms)?;
            }
            Expr::Mul(lhs, rhs) => {
                let mut lhs_terms = HashMap::new();
                let mut rhs_terms = HashMap::new();
                Self::traverse_expr(lhs, multiplier, &mut lhs_terms)?;
                Self::traverse_expr(rhs, multiplier, &mut rhs_terms)?;

                let mut product_terms = HashMap::new();
                for (exp1, coeff1) in lhs_terms {
                    for (exp2, coeff2) in &rhs_terms {
                        let combined_exp = exp1 + *exp2;
                        *product_terms.entry(combined_exp).or_insert(0.0) += coeff1 * coeff2;
                    }
                }

                for (exp, coeff) in product_terms {
                    *terms.entry(exp).or_insert(0.0) += coeff;
                }
            }
            Expr::Div(lhs, rhs) => {
                return Err(SolverError::ParsingError("Unsupported".to_string()));
            }
            Expr::Variable(_) => {
                *terms.entry(1).or_insert(0.0) += multiplier;
            }
            Expr::Number(n) => {
                // Constant term with exponent 0
                *terms.entry(0).or_insert(0.0) += multiplier * n;
            }
            _ => {
                // Handle other expression types or return an error
                return Err(SolverError::NonPolynomial);
            }
        }
        Ok(())
    }
    pub fn traverse_expr_vars(
        expr: &Expr,
        multiplier: f64,
        vars: &mut VarExponents,
    ) -> Result<(), SolverError> {
        match expr {
            Expr::Pow(base, exponent) => {
                if let Expr::Number(exp) = **exponent {
                    if exp.fract() != 0.0 || exp < 0.0 {
                        return Err(SolverError::NonPolynomial);
                    }

                    let exp_u32 = exp as u32;

                    let mut base_vars = VarExponents::new();
                    Self::traverse_expr_vars(base, multiplier, &mut base_vars)?;

                    // Ensure only one variable is present
                    if base_vars.len() != 1 {
                        return Err(SolverError::NonPolynomial);
                    }

                    let (var, var_exp) = base_vars.iter().next().unwrap();
                    let new_exp = var_exp * exp_u32 as i32;
                    let var_key = format!("{}^{}", var, new_exp);

                    *vars.entry(var_key).or_insert(0) += 1;
                } else {
                    return Err(SolverError::NonPolynomial);
                }
            }
            Expr::Add(lhs, rhs) => {
                Self::traverse_expr_vars(lhs, multiplier, vars)?;
                Self::traverse_expr_vars(rhs, multiplier, vars)?;
            }
            Expr::Sub(lhs, rhs) => {
                Self::traverse_expr_vars(lhs, multiplier, vars)?;
                Self::traverse_expr_vars(rhs, -multiplier, vars)?;
            }
            Expr::Mul(lhs, rhs) => {
                // For simplicity, handle multiplication by constants only
                // More complex handling (e.g., multiple variables) can be implemented as needed
                if let Expr::Number(n) = **lhs {
                    Self::traverse_expr_vars(rhs, multiplier * n, vars)?;
                } else if let Expr::Number(n) = **rhs {
                    Self::traverse_expr_vars(lhs, multiplier * n, vars)?;
                } else {
                    return Err(SolverError::NonPolynomial);
                }
            }
            Expr::Div(lhs, rhs) => {
                // Handle division by constants only
                if let Expr::Number(n) = **rhs {
                    Self::traverse_expr_vars(lhs, multiplier / n, vars)?;
                } else {
                    return Err(SolverError::NonPolynomial);
                }
            }
            Expr::Variable(var) => {
                *vars.entry(var.clone()).or_insert(0) += multiplier as i32;
            }
            Expr::Number(n) => {
                // Constants can be treated as variables with exponent 0
                *vars.entry("constant".to_string()).or_insert(0) += 1;
            }
            _ => {
                // Handle other expression types or return an error
                return Err(SolverError::NonPolynomial);
            }
        }
        Ok(())
    }

    /// traverse expressions for solver (collecting polynomial terms)
    pub fn traverse_expr_solver(
        expr: &Expr,
        multiplier: f64,
        terms: &mut HashMap<u32, f64>,
    ) -> Result<(), SolverError> {
        match expr {
            Expr::Pow(base, exponent) => {
                // Handle exponents correctly here
                if let Expr::Number(exp) = **exponent {
                    if exp.fract() != 0.0 || exp < 0.0 {
                        return Err(SolverError::NonPolynomial);
                    }

                    let exp_u32 = exp as u32;

                    // Traverse the base expression
                    let mut base_terms = HashMap::new();
                    Self::traverse_expr_solver(base, multiplier, &mut base_terms)?;

                    // Multiply the exponents by exp_u32
                    for (existing_exp, coeff) in base_terms {
                        let new_exp = existing_exp * exp_u32;
                        *terms.entry(new_exp).or_insert(0.0) += coeff;
                    }
                } else {
                    return Err(SolverError::NonPolynomial);
                }
            }
            Expr::Add(lhs, rhs) => {
                Self::traverse_expr_solver(lhs, multiplier, terms)?;
                Self::traverse_expr_solver(rhs, multiplier, terms)?;
            }
            Expr::Sub(lhs, rhs) => {
                Self::traverse_expr_solver(lhs, multiplier, terms)?;
                Self::traverse_expr_solver(rhs, -multiplier, terms)?;
            }
            Expr::Mul(lhs, rhs) => {
                let mut lhs_terms = HashMap::new();
                let mut rhs_terms = HashMap::new();
                Self::traverse_expr_solver(lhs, multiplier, &mut lhs_terms)?;
                Self::traverse_expr_solver(rhs, multiplier, &mut rhs_terms)?;

                let mut product_terms = HashMap::new();
                for (exp1, coeff1) in lhs_terms {
                    for (exp2, coeff2) in &rhs_terms {
                        let combined_exp = exp1 + exp2;
                        *product_terms.entry(combined_exp).or_insert(0.0) += coeff1 * coeff2;
                    }
                }

                for (exp, coeff) in product_terms {
                    *terms.entry(exp).or_insert(0.0) += coeff;
                }
            }
            Expr::Div(lhs, rhs) => {
                // Handle division by constants only
                if let Expr::Number(n) = **rhs {
                    Self::traverse_expr_solver(lhs, multiplier / n, terms)?;
                } else {
                    return Err(SolverError::NonPolynomial);
                }
            }
            Expr::Variable(_) => {
                // Assume single variable 'x' with exponent 1
                *terms.entry(1).or_insert(0.0) += multiplier;
            }
            Expr::Number(n) => {
                // Constant term with exponent 0
                *terms.entry(0).or_insert(0.0) += multiplier * n;
            }
            _ => {
                // Handle other expression types or return an error
                return Err(SolverError::NonPolynomial);
            }
        }
        Ok(())
    }

    /// Helper function to collect terms from a sub-expression.
    fn _collect_terms_expr(expr: &Expr) -> Result<HashMap<u32, f64>, SolverError> {
        let mut terms = HashMap::new();
        Self::traverse_expr(expr, 1.0, &mut terms)?;
        Ok(terms)
    }

    /// Solves a linear equation ax + b = 0.
    fn solve_linear(polynomial: &Polynomial) -> Result<Solution, SolverError> {
        let a = polynomial.get_coefficient(1);
        let b = polynomial.get_coefficient(0);

        if a == 0.0 {
            if b == 0.0 {
                Ok(Solution::InfiniteSolutions)
            } else {
                Ok(Solution::NoSolution)
            }
        } else {
            let x = -b / a;
            Ok(Solution::SingleSolution(x))
        }
    }

    /// Solves a quadratic equation ax² + bx + c = 0 using the discriminant.
    fn solve_quadratic(polynomial: &Polynomial) -> Result<Solution, SolverError> {
        let a = polynomial.get_coefficient(2);
        let b = polynomial.get_coefficient(1);
        let c = polynomial.get_coefficient(0);

        if a == 0.0 {
            // Degenerates to linear equation
            let linear_poly = Polynomial {
                terms: {
                    let mut terms = HashMap::new();
                    terms.insert(1, b);
                    terms.insert(0, c);
                    terms
                },
            };
            return Self::solve_linear(&linear_poly);
        }

        let discriminant = b * b - 4.0 * a * c;

        if discriminant > 0.0 {
            let sqrt_d = discriminant.sqrt();
            let x1 = (-b + sqrt_d) / (2.0 * a);
            let x2 = (-b - sqrt_d) / (2.0 * a);
            Ok(Solution::MultipleSolutions(vec![x1, x2]))
        } else if discriminant == 0.0 {
            let x = -b / (2.0 * a);
            Ok(Solution::SingleSolution(x))
        } else {
            // TODO: complex solution
            Ok(Solution::Undefined)
        }
    }

    /// Solves a cubic equation ax³ + bx² + cx + d = 0 using Cardano's method.
    fn solve_cubic(polynomial: &Polynomial) -> Result<Solution, SolverError> {
        let a = polynomial.get_coefficient(3);
        let b = polynomial.get_coefficient(2);
        let c = polynomial.get_coefficient(1);
        let d = polynomial.get_coefficient(0);

        if a == 0.0 {
            // Degenerates to quadratic equation
            let quadratic_poly = Polynomial {
                terms: {
                    let mut terms = HashMap::new();
                    terms.insert(2, b);
                    terms.insert(1, c);
                    terms.insert(0, d);
                    terms
                },
            };
            return Self::solve_quadratic(&quadratic_poly);
        }

        // Normalize coefficients
        let b_norm = b / a;
        let c_norm = c / a;
        let d_norm = d / a;

        // Depressed cubic: t^3 + pt + q = 0
        let p = c_norm - b_norm * b_norm / 3.0;
        let q = 2.0 * b_norm.powi(3) / 27.0 - b_norm * c_norm / 3.0 + d_norm;

        let discriminant = (q / 2.0).powi(2) + (p / 3.0).powi(3);

        if discriminant > 0.0 {
            // One real root
            let sqrt_d = discriminant.sqrt();
            let u = ((-q / 2.0) + sqrt_d).cbrt();
            let v = ((-q / 2.0) - sqrt_d).cbrt();
            let t = u + v;
            let x = t - b_norm / 3.0;
            Ok(Solution::SingleSolution(x))
        } else if discriminant == 0.0 {
            // All roots real, at least two equal
            let u = (-q / 2.0).cbrt();
            let t1 = 2.0 * u;
            let t2 = -u;
            let x1 = t1 - b_norm / 3.0;
            let x2 = t2 - b_norm / 3.0;
            if t1 == t2 {
                Ok(Solution::SingleSolution(x1))
            } else {
                Ok(Solution::MultipleSolutions(vec![x1, x2]))
            }
        } else {
            // Three distinct real roots
            let phi = ((-q / 2.0) / ((-p / 3.0).powf(1.5))).acos();
            let t1 = 2.0 * ((-p / 3.0).sqrt()) * phi.cos();
            let t2 = 2.0 * ((-p / 3.0).sqrt()) * (phi + 2.0 * std::f64::consts::PI / 3.0).cos();
            let t3 = 2.0 * ((-p / 3.0).sqrt()) * (phi + 4.0 * std::f64::consts::PI / 3.0).cos();
            let x1 = t1 - b_norm / 3.0;
            let x2 = t2 - b_norm / 3.0;
            let x3 = t3 - b_norm / 3.0;
            Ok(Solution::MultipleSolutions(vec![x1, x2, x3]))
        }
    }
}

/// Builder for the Solver struct.
pub struct SolverBuilder {
    equation: Option<Equation>,
}

impl SolverBuilder {
    /// Creates a new SolverBuilder instance.
    pub fn new() -> Self {
        SolverBuilder { equation: None }
    }

    /// Sets the equation to be solved.
    pub fn equation(mut self, lhs: Expr, rhs: Expr) -> Self {
        self.equation = Some(Equation::new(lhs, rhs));
        self
    }

    /// Builds the Solver instance.
    pub fn build(self) -> Result<Solver, SolverError> {
        match self.equation {
            Some(eq) => Ok(Solver { equation: eq }),
            None => Err(SolverError::InvalidEquation),
        }
    }
}
/// Solves a mathematical equation given as a string.
///
/// # Arguments
///
/// * `equation_str` - A string slice that holds the equation, e.g., "2x + 3 = 7"
///
/// # Returns
///
/// * `Ok(Solution)` if the equation is solved successfully.
/// * `Err(SolverError)` if an error occurs during solving.
pub fn solve_equation(equation_str: &str) -> Result<Solution, SolverError> {
    // Step 1: Split the equation string on '='
    let parts: Vec<&str> = equation_str.split('=').collect();
    if parts.len() != 2 {
        return Err(SolverError::InvalidEquation);
    }

    let lhs_str = parts[0].trim();
    let rhs_str = parts[1].trim();

    // Step 2: Tokenize and parse the left-hand side (lhs)
    let lhs_expr =
        parse_expression(lhs_str).map_err(|e| SolverError::ParsingError(format!("LHS: {}", e)))?;

    // Step 3: Tokenize and parse the right-hand side (rhs)
    let rhs_expr =
        parse_expression(rhs_str).map_err(|e| SolverError::ParsingError(format!("RHS: {}", e)))?;

    // TODO: remove this later
    println!("Parsed LHS Expression: {:?}", lhs_expr);
    println!("Simplified LHS Expression: {}", format_expr(&lhs_expr));
    println!("Parsed RHS Expression: {:?}", rhs_expr);
    println!("Simplified RHS Expression: {}", format_expr(&rhs_expr));

    // Step 4: Build the Solver
    let solver = Solver::builder().equation(lhs_expr, rhs_expr).build()?;

    // Step 5: Solve the equation
    let solution = solver.solve()?;

    Ok(solution)
}

/// Parses and simplifies a mathematical expression from a string.
///
/// # Arguments
///
/// * `expr_str` - A string slice that holds the expression, e.g., "2x + 3"
///
/// # Returns
///
/// * `Ok(Expr)` if the expression is parsed and simplified successfully.
/// * `Err(String)` if an error occurs during tokenization or parsing.
fn parse_expression(expr_str: &str) -> Result<Expr, String> {
    // Tokenize the expression
    let tokens = tokenize(expr_str).map_err(|e| format!("Tokenization error: {}", e))?;
    println!("Tokens: {:?}", tokens);

    // Parse the tokens into an expression (AST)
    let mut parser = Parser::new(tokens);
    let expr = parser
        .parse_expression()
        .map_err(|e| format!("Parsing error: {}", e))?;
    println!("Parsed Expression: {:?}", expr);

    // Simplify the expression
    let simplified_expr = simplify(expr);
    println!("Simplified Expression: {}", format_expr(&simplified_expr));

    Ok(simplified_expr)
}
