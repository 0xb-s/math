#[cfg(test)]
mod tests {

    use crate::ast::Expr;
    use crate::simplify::simplify;

    #[test]
    fn test_simplify_constant() {
        // 2 should remain 2
        let expr = Expr::Number(2.0);
        assert_eq!(simplify(expr), Expr::Number(2.0));
    }

    #[test]
    fn test_simplify_variable() {
        // x should remain x
        let expr = Expr::Variable("x".to_string());
        assert_eq!(simplify(expr), Expr::Variable("x".to_string()));
    }

    #[test]
    fn test_simplify_addition() {
        // 2 + 3 should simplify to 5
        let expr = Expr::Add(Box::new(Expr::Number(2.0)), Box::new(Expr::Number(3.0)));
        assert_eq!(simplify(expr), Expr::Number(5.0));
    }

    #[test]
    fn test_simplify_subtraction() {
        // 5 - 3 should simplify to 2
        let expr = Expr::Sub(Box::new(Expr::Number(5.0)), Box::new(Expr::Number(3.0)));
        assert_eq!(simplify(expr), Expr::Number(2.0));
    }

    #[test]
    fn test_simplify_multiplication() {
        // 2 * 3 should simplify to 6
        let expr = Expr::Mul(Box::new(Expr::Number(2.0)), Box::new(Expr::Number(3.0)));
        assert_eq!(simplify(expr), Expr::Number(6.0));
    }

    #[test]
    fn test_simplify_division() {
        // 6 / 3 should simplify to 2
        let expr = Expr::Div(Box::new(Expr::Number(6.0)), Box::new(Expr::Number(3.0)));
        assert_eq!(simplify(expr), Expr::Number(2.0));
    }

    #[test]
    fn test_simplify_multiplication_by_zero() {
        // x * 0 should simplify to 0
        let expr = Expr::Mul(
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number(0.0)),
        );
        assert_eq!(simplify(expr), Expr::Number(0.0));
    }

    #[test]
    fn test_simplify_multiplication_by_one() {
        // x * 1 should simplify to x
        let expr = Expr::Mul(
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number(1.0)),
        );
        assert_eq!(simplify(expr), Expr::Variable("x".to_string()));
    }

    #[test]
    fn test_simplify_exponents_via_multiplication() {
        // x * x should simplify to x * x (representing x^2)
        let expr = Expr::Mul(
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Variable("x".to_string())),
        );
        assert_eq!(
            simplify(expr),
            Expr::Mul(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Variable("x".to_string()))
            )
        );

        // x * x * x should simplify to x * x * x (representing x^3)
        let expr = Expr::Mul(
            Box::new(Expr::Mul(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Variable("x".to_string())),
            )),
            Box::new(Expr::Variable("x".to_string())),
        );
        assert_eq!(
            simplify(expr),
            Expr::Mul(
                Box::new(Expr::Mul(
                    Box::new(Expr::Variable("x".to_string())),
                    Box::new(Expr::Variable("x".to_string()))
                )),
                Box::new(Expr::Variable("x".to_string()))
            )
        );
    }

    #[test]
    fn test_simplify_zero_variable_expression() {
        // 0 + x should simplify to x
        let expr = Expr::Add(
            Box::new(Expr::Number(0.0)),
            Box::new(Expr::Variable("x".to_string())),
        );
        assert_eq!(simplify(expr), Expr::Variable("x".to_string()));

        // 0 * x should simplify to 0
        let expr = Expr::Mul(
            Box::new(Expr::Number(0.0)),
            Box::new(Expr::Variable("x".to_string())),
        );
        assert_eq!(simplify(expr), Expr::Number(0.0));
    }

    #[test]
    fn test_simplify_multiple_variables_with_exponents() {
        // (x * y) * (x * y) should simplify to x^2 * y^2
        let expr = Expr::Mul(
            Box::new(Expr::Mul(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Variable("y".to_string())),
            )),
            Box::new(Expr::Mul(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Variable("y".to_string())),
            )),
        );
        assert_eq!(
            simplify(expr),
            Expr::Mul(
                Box::new(Expr::Mul(
                    Box::new(Expr::Variable("x".to_string())),
                    Box::new(Expr::Variable("x".to_string()))
                )),
                Box::new(Expr::Mul(
                    Box::new(Expr::Variable("y".to_string())),
                    Box::new(Expr::Variable("y".to_string()))
                ))
            )
        );
    }

    #[test]
    fn test_simplify_expression_with_constants_and_multiple_operations() {
        // (3 + 2) * (x - x) should simplify to 0
        let expr = Expr::Mul(
            Box::new(Expr::Add(
                Box::new(Expr::Number(3.0)),
                Box::new(Expr::Number(2.0)),
            )),
            Box::new(Expr::Sub(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Variable("x".to_string())),
            )),
        );
        assert_eq!(simplify(expr), Expr::Number(0.0));
    }

    #[test]
    fn test_simplify_expression_with_nested_operations() {
        // ((x + x) * (y + y)) / (2 * x * y) should simplify to 2
        let expr = Expr::Div(
            Box::new(Expr::Mul(
                Box::new(Expr::Add(
                    Box::new(Expr::Variable("x".to_string())),
                    Box::new(Expr::Variable("x".to_string())),
                )),
                Box::new(Expr::Add(
                    Box::new(Expr::Variable("y".to_string())),
                    Box::new(Expr::Variable("y".to_string())),
                )),
            )),
            Box::new(Expr::Mul(
                Box::new(Expr::Number(2.0)),
                Box::new(Expr::Mul(
                    Box::new(Expr::Variable("x".to_string())),
                    Box::new(Expr::Variable("y".to_string())),
                )),
            )),
        );
        assert_eq!(simplify(expr), Expr::Number(2.0));
    }

    #[test]
    fn test_simplify_expression_with_multiple_nested_divisions() {
        // (((2 * x) / y) / (x / y)) should simplify to 2
        let expr = Expr::Div(
            Box::new(Expr::Div(
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(2.0)),
                    Box::new(Expr::Variable("x".to_string())),
                )),
                Box::new(Expr::Variable("y".to_string())),
            )),
            Box::new(Expr::Div(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Variable("y".to_string())),
            )),
        );
        assert_eq!(simplify(expr), Expr::Number(2.0));
    }

    #[test]
    fn test_simplify_expression_with_multiple_variables_and_constants() {
        // (4 * x * y) / (2 * x) should simplify to 2 * y
        let expr = Expr::Div(
            Box::new(Expr::Mul(
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(4.0)),
                    Box::new(Expr::Variable("x".to_string())),
                )),
                Box::new(Expr::Variable("y".to_string())),
            )),
            Box::new(Expr::Mul(
                Box::new(Expr::Number(2.0)),
                Box::new(Expr::Variable("x".to_string())),
            )),
        );
        assert_eq!(
            simplify(expr),
            Expr::Mul(
                Box::new(Expr::Number(2.0)),
                Box::new(Expr::Variable("y".to_string()))
            )
        );
    }

    #[test]
    fn test_simplify_expression_with_zero_result() {
        // 5 - (2 + 3) should simplify to 0
        let expr = Expr::Sub(
            Box::new(Expr::Number(5.0)),
            Box::new(Expr::Add(
                Box::new(Expr::Number(2.0)),
                Box::new(Expr::Number(3.0)),
            )),
        );
        assert_eq!(simplify(expr), Expr::Number(0.0));
    }

    #[test]
    fn test_simplify_expression_with_distributive_property() {
        // 2 * (x + 3) should simplify to 2*x + 6
        let expr = Expr::Mul(
            Box::new(Expr::Number(2.0)),
            Box::new(Expr::Add(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Number(3.0)),
            )),
        );
        assert_eq!(
            simplify(expr),
            Expr::Add(
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(2.0)),
                    Box::new(Expr::Variable("x".to_string()))
                )),
                Box::new(Expr::Number(6.0)),
            )
        );
    }

    #[test]
    fn test_simplify_expression_with_multiple_distributive_applications() {
        // (x + y) * (x - y) should simplify to x^2 - y^2
        let expr = Expr::Mul(
            Box::new(Expr::Add(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Variable("y".to_string())),
            )),
            Box::new(Expr::Sub(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Variable("y".to_string())),
            )),
        );
        assert_eq!(
            simplify(expr),
            Expr::Sub(
                Box::new(Expr::Mul(
                    Box::new(Expr::Variable("x".to_string())),
                    Box::new(Expr::Variable("x".to_string()))
                )),
                Box::new(Expr::Mul(
                    Box::new(Expr::Variable("y".to_string())),
                    Box::new(Expr::Variable("y".to_string()))
                ))
            )
        );
    }

    #[test]
    fn test_simplify_expression_with_negative_exponents() {
        // (x / y) * (y / x) should simplify to 1
        let expr = Expr::Mul(
            Box::new(Expr::Div(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Variable("y".to_string())),
            )),
            Box::new(Expr::Div(
                Box::new(Expr::Variable("y".to_string())),
                Box::new(Expr::Variable("x".to_string())),
            )),
        );
        assert_eq!(simplify(expr), Expr::Number(1.0));
    }

    #[test]
    fn test_simplify_expression_with_multiple_nested_operations() {
        // ((x + 2) * (x - 2)) / (x^2 - 4) should simplify to 1
        // Since x^2 - 4 is (x + 2)(x - 2)
        let expr = Expr::Div(
            Box::new(Expr::Mul(
                Box::new(Expr::Add(
                    Box::new(Expr::Variable("x".to_string())),
                    Box::new(Expr::Number(2.0)),
                )),
                Box::new(Expr::Sub(
                    Box::new(Expr::Variable("x".to_string())),
                    Box::new(Expr::Number(2.0)),
                )),
            )),
            Box::new(Expr::Sub(
                Box::new(Expr::Mul(
                    Box::new(Expr::Variable("x".to_string())),
                    Box::new(Expr::Variable("x".to_string())),
                )),
                Box::new(Expr::Number(4.0)),
            )),
        );
        assert_eq!(simplify(expr), Expr::Number(1.0));
    }

    #[test]
    fn test_simplify_expression_with_complex_nested_operations() {
        // ((3 * x) + (2 * y)) - ((x) + (2 * y)) should simplify to 2 * x
        let expr = Expr::Sub(
            Box::new(Expr::Add(
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(3.0)),
                    Box::new(Expr::Variable("x".to_string())),
                )),
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(2.0)),
                    Box::new(Expr::Variable("y".to_string())),
                )),
            )),
            Box::new(Expr::Add(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(2.0)),
                    Box::new(Expr::Variable("y".to_string())),
                )),
            )),
        );
        assert_eq!(
            simplify(expr),
            Expr::Mul(
                Box::new(Expr::Number(2.0)),
                Box::new(Expr::Variable("x".to_string()))
            )
        );
    }

    #[test]
    fn test_simplify_expression_with_nested_multiplications_and_divisions() {
        // (2 * (x / y)) * (3 * (y / x)) should simplify to 6
        let expr = Expr::Mul(
            Box::new(Expr::Mul(
                Box::new(Expr::Number(2.0)),
                Box::new(Expr::Div(
                    Box::new(Expr::Variable("x".to_string())),
                    Box::new(Expr::Variable("y".to_string())),
                )),
            )),
            Box::new(Expr::Mul(
                Box::new(Expr::Number(3.0)),
                Box::new(Expr::Div(
                    Box::new(Expr::Variable("y".to_string())),
                    Box::new(Expr::Variable("x".to_string())),
                )),
            )),
        );
        assert_eq!(simplify(expr), Expr::Number(6.0));
    }

    #[test]
    fn test_simplify_expression_with_multiple_like_terms() {
        // 2x + 2x + 2x should simplify to 6x
        let expr = Expr::Add(
            Box::new(Expr::Add(
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(2.0)),
                    Box::new(Expr::Variable("x".to_string())),
                )),
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(2.0)),
                    Box::new(Expr::Variable("x".to_string())),
                )),
            )),
            Box::new(Expr::Mul(
                Box::new(Expr::Number(2.0)),
                Box::new(Expr::Variable("x".to_string())),
            )),
        );
        assert_eq!(
            simplify(expr),
            Expr::Mul(
                Box::new(Expr::Number(6.0)),
                Box::new(Expr::Variable("x".to_string()))
            )
        );
    }

    #[test]
    fn test_simplify_variable_division() {
        // (2 * x) / x should simplify to 2
        let expr = Expr::Div(
            Box::new(Expr::Mul(
                Box::new(Expr::Number(2.0)),
                Box::new(Expr::Variable("x".to_string())),
            )),
            Box::new(Expr::Variable("x".to_string())),
        );
        assert_eq!(simplify(expr), Expr::Number(2.0));
    }

    #[test]
    fn test_simplify_addition_of_variables() {
        // x + x should simplify to 2 * x
        let expr = Expr::Add(
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Variable("x".to_string())),
        );
        assert_eq!(
            simplify(expr),
            Expr::Mul(
                Box::new(Expr::Number(2.0)),
                Box::new(Expr::Variable("x".to_string()))
            )
        );
    }

    #[test]
    fn test_simplify_subtraction_of_variables() {
        // x - x should simplify to 0
        let expr = Expr::Sub(
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Variable("x".to_string())),
        );
        assert_eq!(simplify(expr), Expr::Number(0.0));
    }

    #[test]
    fn test_simplify_multiplication_of_variables() {
        // x * x should simplify to x^2
        let expr = Expr::Mul(
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Variable("x".to_string())),
        );
        // Expected output: x^2 (which would need to be represented in Expr)
        assert_eq!(
            simplify(expr),
            Expr::Mul(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Variable("x".to_string()))
            )
        );
    }

    #[test]
    fn test_simplify_nested_operations() {
        // (x * 2) + (x * 3) should simplify to 5 * x
        let expr = Expr::Add(
            Box::new(Expr::Mul(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Number(2.0)),
            )),
            Box::new(Expr::Mul(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Number(3.0)),
            )),
        );
        assert_eq!(
            simplify(expr),
            Expr::Mul(
                Box::new(Expr::Number(5.0)),
                Box::new(Expr::Variable("x".to_string()))
            )
        );
    }

    #[test]
    fn test_simplify_complex_expression() {
        // (2 * x) + (x * 3) - (5 * x) should simplify to 0
        let expr = Expr::Sub(
            Box::new(Expr::Add(
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(2.0)),
                    Box::new(Expr::Variable("x".to_string())),
                )),
                Box::new(Expr::Mul(
                    Box::new(Expr::Variable("x".to_string())),
                    Box::new(Expr::Number(3.0)),
                )),
            )),
            Box::new(Expr::Mul(
                Box::new(Expr::Number(5.0)),
                Box::new(Expr::Variable("x".to_string())),
            )),
        );
        assert_eq!(simplify(expr), Expr::Number(0.0));
    }

    #[test]
    fn test_simplify_multiple_variables() {
        // (2 * x * y) / (x * y) should simplify to 2
        let expr = Expr::Div(
            Box::new(Expr::Mul(
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(2.0)),
                    Box::new(Expr::Variable("x".to_string())),
                )),
                Box::new(Expr::Variable("y".to_string())),
            )),
            Box::new(Expr::Mul(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Variable("y".to_string())),
            )),
        );
        assert_eq!(simplify(expr), Expr::Number(2.0));
    }

    #[test]
    fn test_simplify_with_constants_and_variables() {
        // (3 * x) / (2 * x) should simplify to 3/2
        let expr = Expr::Div(
            Box::new(Expr::Mul(
                Box::new(Expr::Number(3.0)),
                Box::new(Expr::Variable("x".to_string())),
            )),
            Box::new(Expr::Mul(
                Box::new(Expr::Number(2.0)),
                Box::new(Expr::Variable("x".to_string())),
            )),
        );
        assert_eq!(simplify(expr), Expr::Number(3.0 / 2.0));
    }

    #[test]
    fn test_simplify_nested_division() {
        // ((2 * x) / y) / (x / y) should simplify to 2
        let expr = Expr::Div(
            Box::new(Expr::Div(
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(2.0)),
                    Box::new(Expr::Variable("x".to_string())),
                )),
                Box::new(Expr::Variable("y".to_string())),
            )),
            Box::new(Expr::Div(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Variable("y".to_string())),
            )),
        );
        assert_eq!(simplify(expr), Expr::Number(2.0));
    }
}
