use std::cmp::Ordering;

use crate::monomial::Monomial;

/// A single term: coefficient * monomial in component `comp` of a free module.
/// For plain ring elements (not module elements), `comp` is always 0.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Term {
    pub coeff: i64,
    pub monom: Monomial,
    pub comp: usize,
}

impl Term {
    pub fn new(coeff: i64, monom: Monomial, comp: usize) -> Self {
        Term { coeff, monom, comp }
    }
}

/// Compare terms for sorting: first by component (ascending),
/// then by monomial in grevlex (descending — larger monomials come first).
fn term_cmp(a: &Term, b: &Term) -> Ordering {
    match a.comp.cmp(&b.comp) {
        Ordering::Equal => a.monom.cmp_grevlex(&b.monom).reverse(),
        other => other,
    }
}

/// A polynomial over ZZ[vars]^r (free module of rank r).
/// Stored as a list of terms sorted in descending order by (component, grevlex).
/// Invariants:
/// - No zero-coefficient terms.
/// - No two terms share the same (monomial, component).
/// - Sorted by `term_cmp` (ascending component, descending grevlex within component).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Poly {
    terms: Vec<Term>,
}

impl Poly {
    /// The zero polynomial.
    pub fn zero() -> Self {
        Poly { terms: Vec::new() }
    }

    /// Create a polynomial from a list of terms. The terms are sorted and
    /// like terms are combined. Zero-coefficient terms are removed.
    pub fn from_terms(mut terms: Vec<Term>) -> Self {
        if terms.is_empty() {
            return Poly::zero();
        }
        // Sort by (component asc, monomial desc in grevlex).
        terms.sort_by(term_cmp);
        // Combine like terms.
        let mut result: Vec<Term> = Vec::with_capacity(terms.len());
        for t in terms {
            if let Some(last) = result.last_mut() {
                if last.comp == t.comp && last.monom == t.monom {
                    last.coeff += t.coeff;
                    continue;
                }
            }
            result.push(t);
        }
        // Remove zeros.
        result.retain(|t| t.coeff != 0);
        Poly { terms: result }
    }

    /// Create a single-term polynomial.
    pub fn from_term(coeff: i64, monom: Monomial, comp: usize) -> Self {
        if coeff == 0 {
            return Poly::zero();
        }
        Poly {
            terms: vec![Term::new(coeff, monom, comp)],
        }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn terms(&self) -> &[Term] {
        &self.terms
    }

    /// The leading term (first in sorted order). Panics if zero.
    pub fn lead_term(&self) -> &Term {
        assert!(!self.is_zero(), "lead_term of zero polynomial");
        &self.terms[0]
    }

    /// The leading coefficient. Panics if zero.
    pub fn lead_coeff(&self) -> i64 {
        self.lead_term().coeff
    }

    /// The leading monomial. Panics if zero.
    pub fn lead_monom(&self) -> &Monomial {
        &self.lead_term().monom
    }

    /// The component of the leading term. Panics if zero.
    pub fn lead_comp(&self) -> usize {
        self.lead_term().comp
    }

    /// Find a term matching the given (monomial, component).
    /// Uses linear search since terms are sorted by (comp, grevlex desc).
    pub fn find_term(&self, monom: &Monomial, comp: usize) -> Option<&Term> {
        self.terms.iter().find(|t| t.comp == comp && t.monom == *monom)
    }

    /// Number of nonzero terms.
    pub fn num_terms(&self) -> usize {
        self.terms.len()
    }

    /// Negate in place.
    pub fn negate(&mut self) {
        for t in &mut self.terms {
            t.coeff = -t.coeff;
        }
    }

    /// Return the negation.
    pub fn negated(&self) -> Poly {
        let mut p = self.clone();
        p.negate();
        p
    }

    /// Multiply all coefficients by a scalar. Removes the result if scalar is 0.
    pub fn scalar_mul(&mut self, c: i64) {
        if c == 0 {
            self.terms.clear();
            return;
        }
        for t in &mut self.terms {
            t.coeff = t.coeff.checked_mul(c).expect("coefficient overflow in scalar_mul");
        }
    }

    /// Divide all coefficients by a scalar (exact division).
    /// Panics if any coefficient is not exactly divisible.
    pub fn scalar_div(&mut self, c: i64) {
        assert!(c != 0, "scalar_div by zero");
        for t in &mut self.terms {
            assert_eq!(t.coeff % c, 0, "scalar_div: {} not divisible by {}", t.coeff, c);
            t.coeff /= c;
        }
    }

    /// Return scalar * self.
    pub fn scalar_muled(&self, c: i64) -> Poly {
        let mut p = self.clone();
        p.scalar_mul(c);
        p
    }

    /// Multiply by a term: coeff * monom * e_{comp}.
    /// For ring elements (comp=0), this multiplies each term's monomial by `monom`
    /// and coefficient by `coeff`. For module elements, this only affects terms
    /// in the given component (but typically we multiply ring polys by a term,
    /// so comp=0 and all terms are affected).
    ///
    /// Actually, in the M2 engine, `mult_by_term` multiplies every term:
    /// new_coeff = coeff * t.coeff, new_monom = monom * t.monom, comp unchanged.
    /// The `comp` parameter is not used for filtering — it's for creating the
    /// output term's component. But in gbvector, mult_by_term uses comp=0 always
    /// (it multiplies a ring element by a term, keeping components).
    ///
    /// We follow the simpler convention: multiply every term's coefficient and
    /// monomial. Component is unchanged.
    pub fn term_mul(&self, coeff: i64, monom: &Monomial) -> Poly {
        if coeff == 0 {
            return Poly::zero();
        }
        let terms: Vec<Term> = self
            .terms
            .iter()
            .map(|t| Term {
                coeff: t.coeff.checked_mul(coeff).expect("coefficient overflow in term_mul"),
                monom: t.monom.mul(monom),
                comp: t.comp,
            })
            .collect();
        // Multiplication by a single term preserves sort order.
        Poly { terms }
    }

    /// Add two polynomials. Merge-based: both are sorted, produce sorted result.
    pub fn add(&self, other: &Poly) -> Poly {
        let mut result = Vec::with_capacity(self.terms.len() + other.terms.len());
        let mut i = 0;
        let mut j = 0;
        while i < self.terms.len() && j < other.terms.len() {
            match term_cmp(&self.terms[i], &other.terms[j]) {
                Ordering::Less => {
                    result.push(self.terms[i].clone());
                    i += 1;
                }
                Ordering::Greater => {
                    result.push(other.terms[j].clone());
                    j += 1;
                }
                Ordering::Equal => {
                    let c = self.terms[i].coeff + other.terms[j].coeff;
                    if c != 0 {
                        result.push(Term {
                            coeff: c,
                            monom: self.terms[i].monom.clone(),
                            comp: self.terms[i].comp,
                        });
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
        while i < self.terms.len() {
            result.push(self.terms[i].clone());
            i += 1;
        }
        while j < other.terms.len() {
            result.push(other.terms[j].clone());
            j += 1;
        }
        Poly { terms: result }
    }

    /// Subtract: self - other.
    pub fn sub(&self, other: &Poly) -> Poly {
        self.add(&other.negated())
    }

    /// Add `coeff * monom * other` to self in place.
    /// This is the core operation used in reduction: f += c * m * g.
    pub fn add_term_mul(&mut self, coeff: i64, monom: &Monomial, other: &Poly) {
        if coeff == 0 || other.is_zero() {
            return;
        }
        let product = other.term_mul(coeff, monom);
        *self = self.add(&product);
    }
}

impl std::fmt::Display for Poly {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_zero() {
            return write!(f, "0");
        }
        for (i, t) in self.terms.iter().enumerate() {
            if i > 0 {
                if t.coeff > 0 {
                    write!(f, " + ")?;
                } else {
                    write!(f, " - ")?;
                }
            } else if t.coeff < 0 {
                write!(f, "-")?;
            }
            let abs_c = t.coeff.abs();
            let mon_is_one = t.monom.is_one();
            if abs_c != 1 || mon_is_one {
                if i > 0 {
                    write!(f, "{}", abs_c)?;
                } else {
                    write!(f, "{}", t.coeff.abs())?;
                }
                if !mon_is_one {
                    write!(f, "*")?;
                }
            }
            if !mon_is_one {
                write!(f, "{}", t.monom)?;
            }
            if t.comp > 0 {
                write!(f, "*e{}", t.comp)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::Monomial;

    // Helper: make a monomial from exponents
    fn m(exps: &[i32]) -> Monomial {
        Monomial::new(exps.to_vec())
    }

    // Helper: make a term
    fn t(coeff: i64, exps: &[i32], comp: usize) -> Term {
        Term::new(coeff, m(exps), comp)
    }

    // Helper: make a poly from (coeff, exps, comp) triples
    fn p(terms: &[(i64, &[i32], usize)]) -> Poly {
        Poly::from_terms(
            terms.iter().map(|(c, e, comp)| t(*c, e, *comp)).collect(),
        )
    }

    // ===== Oracle tests from M2 fixtures =====

    #[test]
    fn test_add_oracle() {
        // f = 3*x^2*y - 2*x*z + 5
        let f = p(&[(3, &[2, 1, 0], 0), (-2, &[1, 0, 1], 0), (5, &[0, 0, 0], 0)]);
        // g = -x^2*y + y^2 + 4*x*z - 3
        let g = p(&[(-1, &[2, 1, 0], 0), (1, &[0, 2, 0], 0), (4, &[1, 0, 1], 0), (-3, &[0, 0, 0], 0)]);
        let sum = f.add(&g);
        // Expected: 2*x^2*y + y^2 + 2*x*z + 2
        let expected = p(&[(2, &[2, 1, 0], 0), (1, &[0, 2, 0], 0), (2, &[1, 0, 1], 0), (2, &[0, 0, 0], 0)]);
        assert_eq!(sum, expected);
    }

    #[test]
    fn test_add_cancel_oracle() {
        // f = 2*x^2 + 3*x*y + z
        let f = p(&[(2, &[2, 0, 0], 0), (3, &[1, 1, 0], 0), (1, &[0, 0, 1], 0)]);
        // g = -2*x^2 - 3*x*y + 2*z
        let g = p(&[(-2, &[2, 0, 0], 0), (-3, &[1, 1, 0], 0), (2, &[0, 0, 1], 0)]);
        let sum = f.add(&g);
        // Expected: 3*z
        let expected = p(&[(3, &[0, 0, 1], 0)]);
        assert_eq!(sum, expected);
    }

    #[test]
    fn test_negate_oracle() {
        let f = p(&[(3, &[2, 1, 0], 0), (-2, &[1, 0, 1], 0), (5, &[0, 0, 0], 0)]);
        let neg = f.negated();
        let expected = p(&[(-3, &[2, 1, 0], 0), (2, &[1, 0, 1], 0), (-5, &[0, 0, 0], 0)]);
        assert_eq!(neg, expected);
    }

    #[test]
    fn test_scalar_mul_oracle() {
        let f = p(&[(3, &[2, 1, 0], 0), (-2, &[1, 0, 1], 0), (5, &[0, 0, 0], 0)]);

        let f3 = f.scalar_muled(3);
        let expected3 = p(&[(9, &[2, 1, 0], 0), (-6, &[1, 0, 1], 0), (15, &[0, 0, 0], 0)]);
        assert_eq!(f3, expected3);

        let fn2 = f.scalar_muled(-2);
        let expectedn2 = p(&[(-6, &[2, 1, 0], 0), (4, &[1, 0, 1], 0), (-10, &[0, 0, 0], 0)]);
        assert_eq!(fn2, expectedn2);
    }

    #[test]
    fn test_term_mul_oracle() {
        // f = 3*x^2*y - 2*x*z + 5
        let f = p(&[(3, &[2, 1, 0], 0), (-2, &[1, 0, 1], 0), (5, &[0, 0, 0], 0)]);
        // Multiply by 2*x*y
        let result = f.term_mul(2, &m(&[1, 1, 0]));
        // Expected: 6*x^3*y^2 - 4*x^2*y*z + 10*x*y
        let expected = p(&[(6, &[3, 2, 0], 0), (-4, &[2, 1, 1], 0), (10, &[1, 1, 0], 0)]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_zero() {
        let z = Poly::zero();
        assert!(z.is_zero());
        assert_eq!(z.num_terms(), 0);
    }

    #[test]
    fn test_lead_term_oracle() {
        let f = p(&[(3, &[2, 1, 0], 0), (-2, &[1, 0, 1], 0), (5, &[0, 0, 0], 0)]);
        assert_eq!(f.lead_coeff(), 3);
        assert_eq!(f.lead_monom(), &m(&[2, 1, 0]));
        assert_eq!(f.lead_comp(), 0);
    }

    #[test]
    fn test_sorting_oracle() {
        // z^2 + x^2 + y^2 + x*y + x*z + y*z — entered in random order
        let f = p(&[
            (1, &[0, 0, 2], 0),
            (1, &[2, 0, 0], 0),
            (1, &[0, 2, 0], 0),
            (1, &[1, 1, 0], 0),
            (1, &[1, 0, 1], 0),
            (1, &[0, 1, 1], 0),
        ]);
        // M2 grevlex order: x^2, x*y, y^2, x*z, y*z, z^2
        let expected_exps: Vec<&[i32]> = vec![
            &[2, 0, 0],
            &[1, 1, 0],
            &[0, 2, 0],
            &[1, 0, 1],
            &[0, 1, 1],
            &[0, 0, 2],
        ];
        let actual_exps: Vec<&[i32]> = f.terms().iter().map(|t| t.monom.exponents()).collect();
        assert_eq!(actual_exps, expected_exps);
    }

    #[test]
    fn test_sub_oracle() {
        let f = p(&[(3, &[2, 1, 0], 0), (-2, &[1, 0, 1], 0), (5, &[0, 0, 0], 0)]);
        let g = p(&[(1, &[2, 1, 0], 0), (4, &[1, 0, 1], 0), (-1, &[0, 0, 0], 0)]);
        let diff = f.sub(&g);
        let expected = p(&[(2, &[2, 1, 0], 0), (-6, &[1, 0, 1], 0), (6, &[0, 0, 0], 0)]);
        assert_eq!(diff, expected);
    }

    // ===== Property-based tests =====

    #[test]
    fn test_add_commutative() {
        let f = p(&[(3, &[2, 1, 0], 0), (-2, &[1, 0, 1], 0), (5, &[0, 0, 0], 0)]);
        let g = p(&[(-1, &[2, 1, 0], 0), (1, &[0, 2, 0], 0), (4, &[1, 0, 1], 0)]);
        assert_eq!(f.add(&g), g.add(&f));
    }

    #[test]
    fn test_add_associative() {
        let f = p(&[(3, &[2, 0, 0], 0), (1, &[0, 0, 1], 0)]);
        let g = p(&[(-1, &[2, 0, 0], 0), (2, &[1, 1, 0], 0)]);
        let h = p(&[(1, &[1, 1, 0], 0), (-1, &[0, 0, 1], 0)]);
        assert_eq!(f.add(&g).add(&h), f.add(&g.add(&h)));
    }

    #[test]
    fn test_add_zero_identity() {
        let f = p(&[(3, &[2, 1, 0], 0), (-2, &[1, 0, 1], 0)]);
        let z = Poly::zero();
        assert_eq!(f.add(&z), f);
        assert_eq!(z.add(&f), f);
    }

    #[test]
    fn test_add_inverse() {
        let f = p(&[(3, &[2, 1, 0], 0), (-2, &[1, 0, 1], 0), (5, &[0, 0, 0], 0)]);
        let neg = f.negated();
        assert!(f.add(&neg).is_zero());
    }

    #[test]
    fn test_scalar_mul_zero() {
        let f = p(&[(3, &[2, 1, 0], 0), (-2, &[1, 0, 1], 0)]);
        assert!(f.scalar_muled(0).is_zero());
    }

    #[test]
    fn test_scalar_mul_one() {
        let f = p(&[(3, &[2, 1, 0], 0), (-2, &[1, 0, 1], 0)]);
        assert_eq!(f.scalar_muled(1), f);
    }

    #[test]
    fn test_display() {
        let f = p(&[(3, &[2, 1, 0], 0), (-2, &[1, 0, 1], 0), (5, &[0, 0, 0], 0)]);
        // [1,0,1] = x0^1 * x1^0 * x2^1 = x0*x2
        assert_eq!(format!("{}", f), "3*x0^2*x1 - 2*x0*x2 + 5");
    }

    #[test]
    fn test_display_zero() {
        assert_eq!(format!("{}", Poly::zero()), "0");
    }

    #[test]
    fn test_from_term_zero_coeff() {
        let p = Poly::from_term(0, m(&[1, 2, 3]), 0);
        assert!(p.is_zero());
    }

    #[test]
    fn test_module_element_sorting() {
        // Terms in different components: component 0 before component 1.
        let f = Poly::from_terms(vec![
            t(1, &[1, 0], 1),
            t(2, &[0, 1], 0),
            t(3, &[1, 0], 0),
        ]);
        assert_eq!(f.terms()[0].comp, 0);
        assert_eq!(f.terms()[0].coeff, 3); // x in comp 0 (higher grevlex)
        assert_eq!(f.terms()[1].comp, 0);
        assert_eq!(f.terms()[1].coeff, 2); // y in comp 0
        assert_eq!(f.terms()[2].comp, 1);
        assert_eq!(f.terms()[2].coeff, 1); // x in comp 1
    }

    #[test]
    fn test_add_term_mul() {
        // f = x^2, then add 2*y * (3*x + 1) = 6*xy + 2*y
        let mut f = p(&[(1, &[2, 0], 0)]);
        let g = p(&[(3, &[1, 0], 0), (1, &[0, 0], 0)]);
        f.add_term_mul(2, &m(&[0, 1]), &g);
        let expected = p(&[(1, &[2, 0], 0), (6, &[1, 1], 0), (2, &[0, 1], 0)]);
        assert_eq!(f, expected);
    }
}
