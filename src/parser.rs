//! Recursive descent parser for polynomials in ZZ[x, y, z, ...].
//!
//! Grammar:
//!   poly      = term (('+' | '-') term)*
//!   term      = ['-'] [integer ['*']] (var_power ('*' var_power)*)?
//!   var_power = var_name ['^' integer]
//!
//! Examples: "3*x^2*y + 2*z - 1", "x^2 - y", "-3", "0"

use crate::monomial::Monomial;
use crate::poly::{Poly, Term};

/// Parser and formatter for polynomials with named variables.
pub struct PolyParser {
    var_names: Vec<String>,
    nvars: usize,
}

impl PolyParser {
    pub fn new(var_names: Vec<String>) -> Self {
        let nvars = var_names.len();
        PolyParser { var_names, nvars }
    }

    pub fn nvars(&self) -> usize {
        self.nvars
    }

    /// Parse a polynomial string. Returns Err on syntax error.
    pub fn parse(&self, input: &str) -> Result<Poly, String> {
        let tokens = tokenize(input)?;
        let mut pos = 0;
        let poly = self.parse_poly(&tokens, &mut pos)?;
        if pos < tokens.len() {
            return Err(format!("unexpected token at position {}: {:?}", pos, tokens[pos]));
        }
        Ok(poly)
    }

    /// Format a polynomial (comp=0 ring element) using variable names.
    pub fn format_poly(&self, poly: &Poly) -> String {
        if poly.is_zero() {
            return "0".to_string();
        }
        let mut result = String::new();
        for (i, t) in poly.terms().iter().enumerate() {
            let abs_c = t.coeff.abs();
            let mon_is_one = t.monom.is_one();

            if i > 0 {
                if t.coeff > 0 {
                    result.push_str(" + ");
                } else {
                    result.push_str(" - ");
                }
            } else if t.coeff < 0 {
                result.push('-');
            }

            if abs_c != 1 || mon_is_one {
                result.push_str(&abs_c.to_string());
                if !mon_is_one {
                    result.push('*');
                }
            }

            if !mon_is_one {
                let mut first_var = true;
                for (j, &e) in t.monom.exponents().iter().enumerate() {
                    if e == 0 {
                        continue;
                    }
                    if !first_var {
                        result.push('*');
                    }
                    first_var = false;
                    result.push_str(&self.var_names[j]);
                    if e > 1 {
                        result.push('^');
                        result.push_str(&e.to_string());
                    }
                }
            }
        }
        result
    }

    /// Format a module element (polynomial with components) as a matrix column.
    /// Returns a vector of polynomials, one per row.
    pub fn format_module_element(&self, poly: &Poly, nrows: usize) -> Vec<String> {
        // Separate terms by component.
        let mut row_polys: Vec<Poly> = (0..nrows).map(|_| Poly::zero()).collect();
        for t in poly.terms() {
            if t.comp < nrows {
                let ring_term = Term::new(t.coeff, t.monom.clone(), 0);
                row_polys[t.comp] = row_polys[t.comp].add(&Poly::from_terms(vec![ring_term]));
            }
        }
        row_polys.iter().map(|p| self.format_poly(p)).collect()
    }

    fn parse_poly(&self, tokens: &[Token], pos: &mut usize) -> Result<Poly, String> {
        let mut terms = Vec::new();
        let mut negate_next = false;

        // Handle leading minus.
        if *pos < tokens.len() && tokens[*pos] == Token::Minus {
            negate_next = true;
            *pos += 1;
        }

        let (coeff, monom) = self.parse_term(tokens, pos)?;
        let c = if negate_next { -coeff } else { coeff };
        terms.push(Term::new(c, monom, 0));

        loop {
            if *pos >= tokens.len() {
                break;
            }
            match tokens[*pos] {
                Token::Plus => {
                    *pos += 1;
                    let (coeff, monom) = self.parse_term(tokens, pos)?;
                    terms.push(Term::new(coeff, monom, 0));
                }
                Token::Minus => {
                    *pos += 1;
                    let (coeff, monom) = self.parse_term(tokens, pos)?;
                    terms.push(Term::new(-coeff, monom, 0));
                }
                _ => break,
            }
        }

        Ok(Poly::from_terms(terms))
    }

    /// Parse a single term (coefficient * monomial product).
    /// Returns (coefficient, monomial).
    fn parse_term(&self, tokens: &[Token], pos: &mut usize) -> Result<(i64, Monomial), String> {
        if *pos >= tokens.len() {
            return Err("expected term, got end of input".to_string());
        }

        let mut coeff: i64 = 1;
        let mut exps = vec![0i32; self.nvars];
        let mut has_coeff = false;
        let mut has_vars = false;

        // Try to parse a number.
        if let Token::Number(n) = tokens[*pos] {
            coeff = n;
            has_coeff = true;
            *pos += 1;

            // Check for '*' followed by variable.
            if *pos < tokens.len() && tokens[*pos] == Token::Star {
                // Peek: is the next thing a variable?
                if *pos + 1 < tokens.len() && matches!(tokens[*pos + 1], Token::Var(_)) {
                    *pos += 1; // consume '*'
                    // Fall through to parse variables.
                } else {
                    // Number alone (or number * number, which is an error).
                    return Ok((coeff, Monomial::new(exps)));
                }
            } else {
                // Number not followed by '*', could be followed by variable directly.
                // e.g. "3x" — we don't support this, require "3*x".
                // But let's be lenient: if next token is a variable, treat as implicit multiply.
                if *pos < tokens.len() && matches!(tokens[*pos], Token::Var(_)) {
                    // implicit multiplication
                } else {
                    return Ok((coeff, Monomial::new(exps)));
                }
            }
        }

        // Parse variable powers.
        while *pos < tokens.len() {
            if let Token::Var(ref name) = tokens[*pos] {
                let var_idx = self.var_index(name)?;
                *pos += 1;
                let exp = if *pos < tokens.len() && tokens[*pos] == Token::Caret {
                    *pos += 1; // consume '^'
                    if *pos < tokens.len() {
                        if let Token::Number(n) = tokens[*pos] {
                            *pos += 1;
                            n as i32
                        } else {
                            return Err(format!("expected exponent after '^'"));
                        }
                    } else {
                        return Err("expected exponent after '^'".to_string());
                    }
                } else {
                    1
                };
                exps[var_idx] += exp;
                has_vars = true;

                // Check for '*' between variables.
                if *pos < tokens.len() && tokens[*pos] == Token::Star {
                    if *pos + 1 < tokens.len() && matches!(tokens[*pos + 1], Token::Var(_)) {
                        *pos += 1; // consume '*'
                    } else {
                        break;
                    }
                }
            } else {
                break;
            }
        }

        if !has_coeff && !has_vars {
            return Err(format!("expected term at position {}", pos));
        }

        Ok((coeff, Monomial::new(exps)))
    }

    fn var_index(&self, name: &str) -> Result<usize, String> {
        self.var_names
            .iter()
            .position(|v| v == name)
            .ok_or_else(|| format!("unknown variable '{}'", name))
    }
}

// ===== Tokenizer =====

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Number(i64),
    Var(String),
    Plus,
    Minus,
    Star,
    Caret,
}

fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let mut tokens = Vec::new();
    let bytes = input.as_bytes();
    let mut i = 0;

    while i < bytes.len() {
        match bytes[i] {
            b' ' | b'\t' | b'\n' | b'\r' => {
                i += 1;
            }
            b'+' => {
                tokens.push(Token::Plus);
                i += 1;
            }
            b'-' => {
                tokens.push(Token::Minus);
                i += 1;
            }
            b'*' => {
                tokens.push(Token::Star);
                i += 1;
            }
            b'^' => {
                tokens.push(Token::Caret);
                i += 1;
            }
            b'0'..=b'9' => {
                let start = i;
                while i < bytes.len() && bytes[i].is_ascii_digit() {
                    i += 1;
                }
                let s = &input[start..i];
                let n: i64 = s.parse().map_err(|e| format!("invalid number '{}': {}", s, e))?;
                tokens.push(Token::Number(n));
            }
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                let start = i;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                tokens.push(Token::Var(input[start..i].to_string()));
            }
            _ => {
                return Err(format!("unexpected character '{}' at position {}", input[i..].chars().next().unwrap(), i));
            }
        }
    }

    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::Monomial;

    fn m(exps: &[i32]) -> Monomial {
        Monomial::new(exps.to_vec())
    }

    fn parser2() -> PolyParser {
        PolyParser::new(vec!["x".to_string(), "y".to_string()])
    }

    fn parser3() -> PolyParser {
        PolyParser::new(vec!["x".to_string(), "y".to_string(), "z".to_string()])
    }

    #[test]
    fn test_parse_constant() {
        let p = parser2();
        let poly = p.parse("42").unwrap();
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.lead_coeff(), 42);
        assert!(poly.lead_monom().is_one());
    }

    #[test]
    fn test_parse_zero() {
        let p = parser2();
        let poly = p.parse("0").unwrap();
        assert!(poly.is_zero());
    }

    #[test]
    fn test_parse_variable() {
        let p = parser2();
        let poly = p.parse("x").unwrap();
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.lead_coeff(), 1);
        assert_eq!(poly.lead_monom(), &m(&[1, 0]));
    }

    #[test]
    fn test_parse_negative() {
        let p = parser2();
        let poly = p.parse("-3").unwrap();
        assert_eq!(poly.lead_coeff(), -3);
    }

    #[test]
    fn test_parse_power() {
        let p = parser2();
        let poly = p.parse("x^2").unwrap();
        assert_eq!(poly.lead_monom(), &m(&[2, 0]));
    }

    #[test]
    fn test_parse_coeff_times_var() {
        let p = parser2();
        let poly = p.parse("3*x^2").unwrap();
        assert_eq!(poly.lead_coeff(), 3);
        assert_eq!(poly.lead_monom(), &m(&[2, 0]));
    }

    #[test]
    fn test_parse_product_of_vars() {
        let p = parser2();
        let poly = p.parse("x*y").unwrap();
        assert_eq!(poly.lead_monom(), &m(&[1, 1]));
    }

    #[test]
    fn test_parse_full_polynomial() {
        let p = parser3();
        let poly = p.parse("3*x^2*y + 2*z - 1").unwrap();
        assert_eq!(poly.num_terms(), 3);
        assert_eq!(poly.lead_coeff(), 3);
        assert_eq!(poly.lead_monom(), &m(&[2, 1, 0]));
    }

    #[test]
    fn test_parse_subtraction() {
        let p = parser2();
        let poly = p.parse("x^2 - y").unwrap();
        assert_eq!(poly.num_terms(), 2);
        // Terms: x^2 (coeff 1), y (coeff -1)
        assert_eq!(poly.terms()[0].coeff, 1);
        assert_eq!(poly.terms()[0].monom, m(&[2, 0]));
        assert_eq!(poly.terms()[1].coeff, -1);
        assert_eq!(poly.terms()[1].monom, m(&[0, 1]));
    }

    #[test]
    fn test_parse_leading_minus() {
        let p = parser2();
        let poly = p.parse("-x^2 + y").unwrap();
        assert_eq!(poly.terms()[0].coeff, -1);
        assert_eq!(poly.terms()[0].monom, m(&[2, 0]));
        assert_eq!(poly.terms()[1].coeff, 1);
    }

    #[test]
    fn test_parse_error_unknown_var() {
        let p = parser2();
        assert!(p.parse("w").is_err());
    }

    #[test]
    fn test_format_poly() {
        let p = parser3();
        let poly = p.parse("3*x^2*y + 2*z - 1").unwrap();
        let s = p.format_poly(&poly);
        assert_eq!(s, "3*x^2*y + 2*z - 1");
    }

    #[test]
    fn test_format_zero() {
        let p = parser2();
        assert_eq!(p.format_poly(&Poly::zero()), "0");
    }

    #[test]
    fn test_format_negative_lead() {
        let p = parser2();
        let poly = p.parse("-x + 1").unwrap();
        // After grevlex sort: -x + 1
        let s = p.format_poly(&poly);
        assert_eq!(s, "-x + 1");
    }

    #[test]
    fn test_roundtrip() {
        let p = parser3();
        let cases = ["x^2 - y", "3*x*y*z + 1", "-5*z^3", "0", "1"];
        for input in &cases {
            let poly = p.parse(input).unwrap();
            let formatted = p.format_poly(&poly);
            let reparsed = p.parse(&formatted).unwrap();
            assert_eq!(poly, reparsed, "roundtrip failed for '{}'", input);
        }
    }

    #[test]
    fn test_parse_implicit_mul() {
        // "3x" without explicit '*'
        let p = parser2();
        let poly = p.parse("3x^2").unwrap();
        assert_eq!(poly.lead_coeff(), 3);
        assert_eq!(poly.lead_monom(), &m(&[2, 0]));
    }
}
