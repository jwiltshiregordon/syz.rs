use std::cmp::Ordering;

/// Exponent vector representing a monomial x1^a1 * x2^a2 * ... * xn^an.
///
/// All monomials in a computation share the same number of variables (`nvars`).
/// Exponents are stored as `i32` (matching M2's convention; negative exponents
/// can arise internally during division).
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Monomial {
    exponents: Vec<i32>,
}

impl Monomial {
    /// Create a monomial from an exponent vector.
    pub fn new(exponents: Vec<i32>) -> Self {
        Monomial { exponents }
    }

    /// The identity monomial (all exponents zero) in `n` variables.
    pub fn one(n: usize) -> Self {
        Monomial {
            exponents: vec![0; n],
        }
    }

    pub fn nvars(&self) -> usize {
        self.exponents.len()
    }

    pub fn exponents(&self) -> &[i32] {
        &self.exponents
    }

    /// Total degree: sum of exponents.
    pub fn total_degree(&self) -> i32 {
        self.exponents.iter().sum()
    }

    /// Weighted degree with given weight vector.
    pub fn weighted_degree(&self, weights: &[i32]) -> i32 {
        assert_eq!(self.exponents.len(), weights.len());
        self.exponents.iter().zip(weights).map(|(e, w)| e * w).sum()
    }

    /// Monomial multiplication: add exponent vectors component-wise.
    pub fn mul(&self, other: &Monomial) -> Monomial {
        assert_eq!(self.nvars(), other.nvars());
        Monomial {
            exponents: self
                .exponents
                .iter()
                .zip(&other.exponents)
                .map(|(a, b)| a + b)
                .collect(),
        }
    }

    /// Monomial division: subtract exponent vectors component-wise.
    /// Caller must ensure `other` divides `self` (or accept negative exponents).
    pub fn div(&self, other: &Monomial) -> Monomial {
        assert_eq!(self.nvars(), other.nvars());
        Monomial {
            exponents: self
                .exponents
                .iter()
                .zip(&other.exponents)
                .map(|(a, b)| a - b)
                .collect(),
        }
    }

    /// Does `self` divide `other`? (All exponents of self ≤ corresponding exponents of other.)
    pub fn divides(&self, other: &Monomial) -> bool {
        assert_eq!(self.nvars(), other.nvars());
        self.exponents
            .iter()
            .zip(&other.exponents)
            .all(|(a, b)| a <= b)
    }

    /// Least common multiple: component-wise max of exponents.
    pub fn lcm(&self, other: &Monomial) -> Monomial {
        assert_eq!(self.nvars(), other.nvars());
        Monomial {
            exponents: self
                .exponents
                .iter()
                .zip(&other.exponents)
                .map(|(a, b)| *a.max(b))
                .collect(),
        }
    }

    /// Greatest common divisor: component-wise min of exponents.
    pub fn gcd(&self, other: &Monomial) -> Monomial {
        assert_eq!(self.nvars(), other.nvars());
        Monomial {
            exponents: self
                .exponents
                .iter()
                .zip(&other.exponents)
                .map(|(a, b)| *a.min(b))
                .collect(),
        }
    }

    /// Graded reverse lexicographic (grevlex) comparison.
    ///
    /// First compare total degree (higher is greater).
    /// Then break ties by reverse lex: scan exponents from the *last* variable
    /// toward the first; the monomial with the *smaller* exponent at the first
    /// difference is *greater* in grevlex.
    pub fn cmp_grevlex(&self, other: &Monomial) -> Ordering {
        assert_eq!(self.nvars(), other.nvars());
        let deg_cmp = self.total_degree().cmp(&other.total_degree());
        if deg_cmp != Ordering::Equal {
            return deg_cmp;
        }
        // Reverse lex: scan from last variable backward.
        // The one with SMALLER exponent at the first difference is GREATER.
        for i in (0..self.nvars()).rev() {
            match self.exponents[i].cmp(&other.exponents[i]) {
                Ordering::Less => return Ordering::Greater,
                Ordering::Greater => return Ordering::Less,
                Ordering::Equal => continue,
            }
        }
        Ordering::Equal
    }

    /// Returns true if this is the identity monomial (all exponents zero).
    pub fn is_one(&self) -> bool {
        self.exponents.iter().all(|&e| e == 0)
    }
}

impl std::fmt::Display for Monomial {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for (i, &e) in self.exponents.iter().enumerate() {
            if e == 0 {
                continue;
            }
            if !first {
                write!(f, "*")?;
            }
            first = false;
            if e == 1 {
                write!(f, "x{}", i)?;
            } else {
                write!(f, "x{}^{}", i, e)?;
            }
        }
        if first {
            write!(f, "1")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_one() {
        let m = Monomial::one(3);
        assert_eq!(m.exponents(), &[0, 0, 0]);
        assert!(m.is_one());
        assert_eq!(m.total_degree(), 0);
    }

    #[test]
    fn test_mul() {
        // x0^2 * x1 * x0 * x1^3 = x0^3 * x1^4
        let a = Monomial::new(vec![2, 1, 0]);
        let b = Monomial::new(vec![1, 3, 0]);
        let c = a.mul(&b);
        assert_eq!(c.exponents(), &[3, 4, 0]);
    }

    #[test]
    fn test_div() {
        let a = Monomial::new(vec![3, 4, 2]);
        let b = Monomial::new(vec![1, 2, 0]);
        let c = a.div(&b);
        assert_eq!(c.exponents(), &[2, 2, 2]);
    }

    #[test]
    fn test_divides() {
        let a = Monomial::new(vec![1, 2, 0]);
        let b = Monomial::new(vec![3, 4, 2]);
        assert!(a.divides(&b));
        assert!(!b.divides(&a));

        // Self divides self.
        assert!(a.divides(&a));

        // 1 divides everything.
        let one = Monomial::one(3);
        assert!(one.divides(&a));
        assert!(one.divides(&b));
    }

    #[test]
    fn test_lcm_gcd() {
        let a = Monomial::new(vec![3, 1, 4]);
        let b = Monomial::new(vec![1, 5, 2]);
        let l = a.lcm(&b);
        let g = a.gcd(&b);
        assert_eq!(l.exponents(), &[3, 5, 4]);
        assert_eq!(g.exponents(), &[1, 1, 2]);

        // Properties: lcm divisible by both, gcd divides both.
        assert!(a.divides(&l));
        assert!(b.divides(&l));
        assert!(g.divides(&a));
        assert!(g.divides(&b));
    }

    #[test]
    fn test_grevlex_total_degree() {
        // Different total degrees: higher degree is greater.
        let a = Monomial::new(vec![2, 1, 0]); // deg 3
        let b = Monomial::new(vec![1, 0, 0]); // deg 1
        assert_eq!(a.cmp_grevlex(&b), Ordering::Greater);
        assert_eq!(b.cmp_grevlex(&a), Ordering::Less);
    }

    #[test]
    fn test_grevlex_same_degree() {
        // In ZZ[x, y, z] with grevlex:
        // x^2 > xy > y^2 > xz > yz > z^2
        let x2 = Monomial::new(vec![2, 0, 0]);
        let xy = Monomial::new(vec![1, 1, 0]);
        let y2 = Monomial::new(vec![0, 2, 0]);
        let xz = Monomial::new(vec![1, 0, 1]);
        let yz = Monomial::new(vec![0, 1, 1]);
        let z2 = Monomial::new(vec![0, 0, 2]);

        let mons = [&x2, &xy, &y2, &xz, &yz, &z2];
        // Check each consecutive pair.
        for i in 0..mons.len() - 1 {
            assert_eq!(
                mons[i].cmp_grevlex(mons[i + 1]),
                Ordering::Greater,
                "{} should be > {}",
                mons[i],
                mons[i + 1]
            );
        }
    }

    #[test]
    fn test_grevlex_equal() {
        let a = Monomial::new(vec![1, 2, 3]);
        assert_eq!(a.cmp_grevlex(&a), Ordering::Equal);
    }

    #[test]
    fn test_grevlex_degree3_three_vars() {
        // Full ordering of degree-3 monomials in grevlex for 3 vars:
        // x^3 > x^2y > xy^2 > y^3 > x^2z > xyz > y^2z > xz^2 > yz^2 > z^3
        let expected: Vec<Monomial> = vec![
            Monomial::new(vec![3, 0, 0]),
            Monomial::new(vec![2, 1, 0]),
            Monomial::new(vec![1, 2, 0]),
            Monomial::new(vec![0, 3, 0]),
            Monomial::new(vec![2, 0, 1]),
            Monomial::new(vec![1, 1, 1]),
            Monomial::new(vec![0, 2, 1]),
            Monomial::new(vec![1, 0, 2]),
            Monomial::new(vec![0, 1, 2]),
            Monomial::new(vec![0, 0, 3]),
        ];

        for i in 0..expected.len() {
            for j in (i + 1)..expected.len() {
                assert_eq!(
                    expected[i].cmp_grevlex(&expected[j]),
                    Ordering::Greater,
                    "{} should be > {}",
                    expected[i],
                    expected[j]
                );
            }
        }
    }

    #[test]
    fn test_weighted_degree() {
        let m = Monomial::new(vec![2, 3, 1]);
        assert_eq!(m.weighted_degree(&[1, 1, 1]), 6); // total degree
        assert_eq!(m.weighted_degree(&[2, 1, 3]), 10); // 2*2 + 3*1 + 1*3
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", Monomial::one(3)), "1");
        assert_eq!(format!("{}", Monomial::new(vec![1, 0, 0])), "x0");
        assert_eq!(format!("{}", Monomial::new(vec![2, 0, 3])), "x0^2*x2^3");
        assert_eq!(format!("{}", Monomial::new(vec![1, 1, 1])), "x0*x1*x2");
    }

    /// Property: lcm(a, b) is divisible by both a and b, and any monomial
    /// divisible by both a and b is divisible by lcm(a, b).
    #[test]
    fn test_lcm_property() {
        let cases = vec![
            (vec![0, 0, 0], vec![0, 0, 0]),
            (vec![1, 2, 3], vec![3, 2, 1]),
            (vec![5, 0, 0], vec![0, 0, 5]),
            (vec![1, 1, 1], vec![2, 2, 2]),
        ];
        for (ea, eb) in cases {
            let a = Monomial::new(ea);
            let b = Monomial::new(eb);
            let l = a.lcm(&b);
            assert!(a.divides(&l));
            assert!(b.divides(&l));
            // lcm should be the *least* such: lcm divides any common multiple.
            // The product a*b is a common multiple.
            let prod = a.mul(&b);
            assert!(l.divides(&prod));
        }
    }

    /// Property: gcd(a, b) divides both a and b.
    #[test]
    fn test_gcd_property() {
        let cases = vec![
            (vec![0, 0, 0], vec![0, 0, 0]),
            (vec![1, 2, 3], vec![3, 2, 1]),
            (vec![5, 0, 0], vec![0, 0, 5]),
        ];
        for (ea, eb) in cases {
            let a = Monomial::new(ea);
            let b = Monomial::new(eb);
            let g = a.gcd(&b);
            assert!(g.divides(&a));
            assert!(g.divides(&b));
        }
    }

    /// Property: grevlex is consistent with multiplication.
    /// If a > b in grevlex, then a*m > b*m for any monomial m.
    #[test]
    fn test_grevlex_consistent_with_mul() {
        let a = Monomial::new(vec![2, 0, 0]);
        let b = Monomial::new(vec![1, 1, 0]);
        assert_eq!(a.cmp_grevlex(&b), Ordering::Greater);

        let multipliers = vec![
            Monomial::new(vec![1, 0, 0]),
            Monomial::new(vec![0, 1, 0]),
            Monomial::new(vec![0, 0, 1]),
            Monomial::new(vec![1, 1, 1]),
        ];
        for m in &multipliers {
            let am = a.mul(m);
            let bm = b.mul(m);
            assert_eq!(
                am.cmp_grevlex(&bm),
                Ordering::Greater,
                "{}*{} should be > {}*{}",
                a,
                m,
                b,
                m
            );
        }
    }
}
