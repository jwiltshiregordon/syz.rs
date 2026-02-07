//! Integer (ZZ) coefficient operations for Buchberger's algorithm.
//!
//! Key operations:
//! - `gcd(a, b)`: greatest common divisor (always non-negative)
//! - `syzygy(a, b) -> (x, y)`: find x, y with ax + by = 0
//! - `balanced_rem(a, b)`: remainder in (-|b|/2, |b|/2]
//! - `content(coeffs)`: gcd of a list of integers (always positive)

use crate::poly::Poly;

/// Greatest common divisor, always non-negative.
/// gcd(0, 0) = 0 by convention.
pub fn gcd(a: i64, b: i64) -> i64 {
    let mut a = a.abs();
    let mut b = b.abs();
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Find (x, y) such that ax + by = 0.
///
/// Follows M2's sign convention:
/// - If a == 0: returns (1, 0)
/// - If b == 1: returns (1, -a)
/// - If b == -1: returns (1, a)
/// - Otherwise: g = gcd(a,b), x = b/g, y = a/g, then adjust signs
///   so that x > 0 (negate y) or x < 0 (negate x to make it positive).
///
/// Panics if b == 0.
pub fn syzygy(a: i64, b: i64) -> (i64, i64) {
    assert!(b != 0, "syzygy: b must be nonzero");

    if a == 0 {
        return (1, 0);
    }
    if b == 1 {
        return (1, -a);
    }
    if b == -1 {
        return (1, a);
    }

    let g = gcd(a, b);
    let mut x = b / g;
    let mut y = a / g;

    // Adjust signs so that ax + by = 0.
    // Currently x = b/g, y = a/g, so a*(b/g) + b*(a/g) = 2ab/g ≠ 0.
    // We need ax + by = 0, i.e., x = -b/g, y = a/g (then a*(-b/g) + b*(a/g) = 0).
    // But M2 normalizes: if x > 0, negate y; else negate x.
    // Starting from x = b/g, y = a/g:
    if x > 0 {
        y = -y;
    } else {
        x = -x;
    }
    // Now we have ax + by = a*(|b|/g) + b*(-sign(b)*a/g)
    // Let's verify: if b > 0, x = b/g > 0, so y = -a/g.
    //   ax + by = a*b/g + b*(-a/g) = 0. ✓
    // If b < 0, x = b/g < 0, so x = -x = -b/g = |b|/g > 0,
    //   and y stays as a/g. ax + by = a*|b|/g + b*a/g = a|b|/g - |b|a/g = 0. ✓

    (x, y)
}

/// Quotient and remainder: a = q*b + r, with r having the same sign as b
/// (Euclidean division matching Rust's div_euclid/rem_euclid is not what M2 uses).
///
/// Actually M2 uses floor division (remainder has same sign as divisor),
/// which matches Rust's `div_euclid` / `rem_euclid` for positive divisor,
/// but for negative divisor the conventions may differ.
///
/// For our purposes we match M2's convention: r = a % b where r >= 0 when b > 0.
/// M2's `//` and `%` use floor division.
pub fn div_rem(a: i64, b: i64) -> (i64, i64) {
    assert!(b != 0, "div_rem: division by zero");
    // Rust's a.div_euclid(b) gives quotient with non-negative remainder
    // for positive b, which matches M2. For negative b, M2 also gives
    // non-negative remainder.
    let q = a.div_euclid(b);
    let r = a.rem_euclid(b);
    (q, r)
}

/// Balanced remainder: r in (-|b|/2, |b|/2].
/// This is used in ZZ reduction to keep coefficients small.
pub fn balanced_rem(a: i64, b: i64) -> i64 {
    assert!(b != 0, "balanced_rem: division by zero");
    let abs_b = b.abs();
    let r = a.rem_euclid(abs_b);
    // r is in [0, |b|). We want it in (-|b|/2, |b|/2].
    if 2 * r > abs_b {
        r - abs_b
    } else {
        r
    }
}

/// Extended GCD: returns (g, u, v) with u*a + v*b = g and g >= 0.
pub fn extended_gcd(a: i64, b: i64) -> (i64, i64, i64) {
    if b == 0 {
        if a >= 0 {
            return (a, 1, 0);
        } else {
            return (-a, -1, 0);
        }
    }
    // Iterative extended Euclidean algorithm.
    let mut old_r = a;
    let mut r = b;
    let mut old_s: i64 = 1;
    let mut s: i64 = 0;
    let mut old_t: i64 = 0;
    let mut t: i64 = 1;
    while r != 0 {
        let q = old_r / r;
        let tmp = r;
        r = old_r - q * r;
        old_r = tmp;
        let tmp = s;
        s = old_s - q * s;
        old_s = tmp;
        let tmp = t;
        t = old_t - q * t;
        old_t = tmp;
    }
    // old_r = gcd, old_s = u, old_t = v, but gcd might be negative.
    if old_r < 0 {
        (-old_r, -old_s, -old_t)
    } else {
        (old_r, old_s, old_t)
    }
}

/// Balanced quotient: a = q*b + balanced_rem(a, b).
pub fn balanced_div(a: i64, b: i64) -> i64 {
    (a - balanced_rem(a, b)) / b
}

/// Content of a polynomial: gcd of all coefficients, always positive.
/// Returns 0 for the zero polynomial.
pub fn poly_content(f: &Poly) -> i64 {
    if f.is_zero() {
        return 0;
    }
    let mut g: i64 = 0;
    for t in f.terms() {
        g = gcd(g, t.coeff);
        if g == 1 {
            return 1;
        }
    }
    g
}

/// Remove the content from a polynomial: divide all coefficients by gcd.
/// Returns the content. The polynomial becomes primitive (content = 1).
/// Does nothing to the zero polynomial (returns 0).
pub fn poly_remove_content(f: &mut Poly) -> i64 {
    let c = poly_content(f);
    if c <= 1 {
        return c;
    }
    f.scalar_div(c);
    c
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::Monomial;
    use crate::poly::{Poly, Term};

    fn m(exps: &[i32]) -> Monomial {
        Monomial::new(exps.to_vec())
    }

    fn p(terms: &[(i64, &[i32], usize)]) -> Poly {
        Poly::from_terms(
            terms
                .iter()
                .map(|(c, e, comp)| Term::new(*c, m(e), *comp))
                .collect(),
        )
    }

    // ===== GCD oracle tests =====

    #[test]
    fn test_gcd_oracle() {
        assert_eq!(gcd(6, 4), 2);
        assert_eq!(gcd(12, 8), 4);
        assert_eq!(gcd(7, 3), 1);
        assert_eq!(gcd(0, 5), 5);
        assert_eq!(gcd(5, 0), 5);
        assert_eq!(gcd(1, 1), 1);
        assert_eq!(gcd(-6, 4), 2);
        assert_eq!(gcd(15, 10), 5);
        assert_eq!(gcd(100, 35), 5);
        assert_eq!(gcd(0, 0), 0);
    }

    // ===== Syzygy oracle tests =====

    #[test]
    fn test_syzygy_oracle() {
        // These match the C++ RingZZ::syzygy convention (x > 0),
        // which differs by a global sign from M2's `syz` command output.
        // The ring-level convention is: g = gcd(a,b), x = b/g, y = a/g,
        // then if x > 0, negate y; else negate x. So x is always > 0
        // (except when a = 0 → x = 1).
        let cases: Vec<(i64, i64, (i64, i64))> = vec![
            (6, 4, (2, -3)),       // g=2, x=2, y=-3
            (12, 8, (2, -3)),      // g=4, x=2, y=-3
            (7, 3, (3, -7)),       // g=1, x=3, y=-7
            (1, 1, (1, -1)),       // b=1 special case
            (0, 5, (1, 0)),        // a=0 special case
            (-6, 4, (2, 3)),       // g=2, x=4/2=2>0, negate y: y=-(-3)=3
            (6, -4, (2, 3)),       // g=2, x=-4/2=-2<0, negate x→2, y=6/2=3
            (-6, -4, (2, -3)),     // g=2, x=-4/2=-2<0, negate x→2, y=-6/2=-3
            (15, 10, (2, -3)),     // g=5, x=2, y=-3
            (100, 35, (7, -20)),   // g=5, x=7, y=-20
        ];
        for (a, b, expected) in &cases {
            let (x, y) = syzygy(*a, *b);
            assert_eq!(
                (x, y), *expected,
                "syzygy({}, {}) = ({}, {}), expected ({}, {})",
                a, b, x, y, expected.0, expected.1
            );
            // Always verify the syzygy relation.
            assert_eq!(
                a * x + b * y,
                0,
                "syzygy relation failed for ({}, {}): {}*{} + {}*{} = {}",
                a, b, a, x, b, y, a * x + b * y
            );
        }
    }

    #[test]
    fn test_syzygy_property_relation() {
        // For any (a, b) with b != 0, syzygy(a, b) = (x, y) with ax + by = 0.
        let cases: Vec<(i64, i64)> = vec![
            (1, 2), (3, 5), (100, 7), (-13, 4), (0, 3), (42, 6),
            (-100, -35), (17, 17), (1, 100),
        ];
        for (a, b) in cases {
            let (x, y) = syzygy(a, b);
            assert_eq!(a * x + b * y, 0, "syzygy({}, {}): {}*{} + {}*{} != 0", a, b, a, x, b, y);
        }
    }

    // ===== Div/rem oracle tests =====

    #[test]
    fn test_div_rem_oracle() {
        let cases: Vec<(i64, i64, (i64, i64))> = vec![
            (17, 5, (3, 2)),
            (-17, 5, (-4, 3)),
            (17, -5, (-3, 2)),
            (-17, -5, (4, 3)),
            (10, 3, (3, 1)),
            (-10, 3, (-4, 2)),
            (0, 7, (0, 0)),
            (7, 1, (7, 0)),
            (15, 5, (3, 0)),
        ];
        for (a, b, (eq, er)) in &cases {
            let (q, r) = div_rem(*a, *b);
            assert_eq!((q, r), (*eq, *er), "div_rem({}, {})", a, b);
            assert_eq!(q * b + r, *a, "div_rem relation for ({}, {})", a, b);
        }
    }

    // ===== Balanced remainder tests =====

    #[test]
    fn test_balanced_rem() {
        // balanced_rem(a, b) should be in (-|b|/2, |b|/2]
        assert_eq!(balanced_rem(7, 5), 2);    // 7 = 1*5 + 2
        assert_eq!(balanced_rem(8, 5), -2);   // 8 = 2*5 + (-2)
        assert_eq!(balanced_rem(10, 5), 0);   // exact
        assert_eq!(balanced_rem(-7, 5), -2);  // -7 = -1*5 + (-2)
        assert_eq!(balanced_rem(3, 6), 3);    // 3 = 0*6 + 3 (3 = |6|/2, on boundary: stays)
        assert_eq!(balanced_rem(4, 6), -2);   // 4 = 1*6 + (-2)
        assert_eq!(balanced_rem(0, 5), 0);
    }

    #[test]
    fn test_balanced_rem_property() {
        // For any a, b: |balanced_rem(a, b)| <= |b|/2
        // and a = balanced_div(a, b) * b + balanced_rem(a, b)
        let vals: Vec<i64> = vec![-20, -7, -1, 0, 1, 3, 7, 13, 20];
        let divs: Vec<i64> = vec![1, 2, 3, 5, 7, 10];
        for &a in &vals {
            for &b in &divs {
                let r = balanced_rem(a, b);
                let q = balanced_div(a, b);
                assert_eq!(q * b + r, a, "balanced div/rem relation for ({}, {})", a, b);
                assert!(
                    2 * r.abs() <= b.abs(),
                    "balanced_rem({}, {}) = {} out of range",
                    a, b, r
                );
            }
        }
    }

    // ===== Content oracle tests =====

    #[test]
    fn test_content_oracle() {
        // 6*x^2 + 4*x*y + 2 → content 2
        let f = p(&[(6, &[2, 0, 0], 0), (4, &[1, 1, 0], 0), (2, &[0, 0, 0], 0)]);
        assert_eq!(poly_content(&f), 2);

        // -15*x^2*y + 10*x - 5 → content 5
        let f = p(&[(-15, &[2, 1, 0], 0), (10, &[1, 0, 0], 0), (-5, &[0, 0, 0], 0)]);
        assert_eq!(poly_content(&f), 5);

        // 7*x + 3*y → content 1
        let f = p(&[(7, &[1, 0, 0], 0), (3, &[0, 1, 0], 0)]);
        assert_eq!(poly_content(&f), 1);

        // x + y + z → content 1
        let f = p(&[(1, &[1, 0, 0], 0), (1, &[0, 1, 0], 0), (1, &[0, 0, 1], 0)]);
        assert_eq!(poly_content(&f), 1);

        // zero polynomial → content 0
        assert_eq!(poly_content(&Poly::zero()), 0);
    }

    #[test]
    fn test_remove_content_oracle() {
        // 6*x^2 + 4*x*y + 2 → primitive part 3*x^2 + 2*x*y + 1
        let mut f = p(&[(6, &[2, 0, 0], 0), (4, &[1, 1, 0], 0), (2, &[0, 0, 0], 0)]);
        let c = poly_remove_content(&mut f);
        assert_eq!(c, 2);
        let expected = p(&[(3, &[2, 0, 0], 0), (2, &[1, 1, 0], 0), (1, &[0, 0, 0], 0)]);
        assert_eq!(f, expected);

        // -15*x^2*y + 10*x - 5 → -3*x^2*y + 2*x - 1
        let mut f = p(&[(-15, &[2, 1, 0], 0), (10, &[1, 0, 0], 0), (-5, &[0, 0, 0], 0)]);
        let c = poly_remove_content(&mut f);
        assert_eq!(c, 5);
        let expected = p(&[(-3, &[2, 1, 0], 0), (2, &[1, 0, 0], 0), (-1, &[0, 0, 0], 0)]);
        assert_eq!(f, expected);
    }

    // ===== Extended GCD tests =====

    #[test]
    fn test_extended_gcd_oracle() {
        let cases: Vec<(i64, i64, i64)> = vec![
            (6, 4, 2),
            (12, 8, 4),
            (7, 3, 1),
            (0, 5, 5),
            (5, 0, 5),
            (-6, 4, 2),
            (15, 10, 5),
            (100, 35, 5),
            (0, 0, 0),
            (1, 1, 1),
        ];
        for (a, b, expected_g) in &cases {
            let (g, u, v) = extended_gcd(*a, *b);
            assert_eq!(g, *expected_g, "extended_gcd({}, {}).0 = {}, expected {}", a, b, g, expected_g);
            assert_eq!(u * a + v * b, g, "extended_gcd({}, {}): {}*{} + {}*{} = {} != {}", a, b, u, a, v, b, u * a + v * b, g);
        }
    }

    #[test]
    fn test_extended_gcd_property() {
        let vals: Vec<i64> = vec![-20, -7, -1, 0, 1, 3, 7, 13, 20];
        for &a in &vals {
            for &b in &vals {
                let (g, u, v) = extended_gcd(a, b);
                assert!(g >= 0, "gcd should be non-negative");
                assert_eq!(u * a + v * b, g, "Bezout relation failed for ({}, {})", a, b);
                assert_eq!(g, gcd(a, b), "extended_gcd gcd doesn't match gcd for ({}, {})", a, b);
            }
        }
    }

    #[test]
    fn test_gcd_property() {
        // gcd(a, b) divides both a and b
        let cases: Vec<(i64, i64)> = vec![
            (6, 4), (12, 8), (0, 5), (5, 0), (100, 35), (-6, 4), (0, 0),
        ];
        for (a, b) in cases {
            let g = gcd(a, b);
            if g != 0 {
                assert_eq!(a % g, 0, "gcd({}, {}) = {} does not divide {}", a, b, g, a);
                assert_eq!(b % g, 0, "gcd({}, {}) = {} does not divide {}", a, b, g, b);
            }
            assert!(g >= 0, "gcd should be non-negative");
        }
    }
}
