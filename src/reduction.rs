//! Reduction operations over ZZ for the Buchberger algorithm.
//!
//! Over ZZ, we cannot divide lead coefficients exactly, so reduction uses
//! balanced remainder. Additional GCD-based operations (`replace_2by2_zz`,
//! `combine_lead_terms_zz`) prevent coefficient blowup.

use crate::monomial::Monomial;
use crate::poly::Poly;
use crate::zz::{balanced_div, balanced_rem, extended_gcd, syzygy};

/// Compute monomials (m1, m2) such that m1 * a == m2 * b == lcm(a, b).
pub fn exponent_syzygy(a: &Monomial, b: &Monomial) -> (Monomial, Monomial) {
    let l = a.lcm(b);
    (l.div(a), l.div(b))
}

/// Single-step lead term reduction over ZZ.
///
/// Precondition: lt(g).monom divides lt(f).monom, same component.
///
/// Computes v = -(balanced_div(lc(f), lc(g))) and adds v * m * g to f,
/// where m = lt(f).monom / lt(g).monom. Tracks syzygy in fsyz.
///
/// Returns true if the lead term was fully cancelled (balanced_rem == 0),
/// false if a non-zero balanced remainder was left behind (or v == 0).
pub fn reduce_lead_term_zz(f: &mut Poly, fsyz: &mut Poly, g: &Poly, gsyz: &Poly) -> bool {
    assert!(!f.is_zero() && !g.is_zero());

    let lc_f = f.lead_coeff();
    let lc_g = g.lead_coeff();
    let v = -balanced_div(lc_f, lc_g);
    if v == 0 {
        return false;
    }

    let m = f.lead_monom().div(g.lead_monom());
    f.add_term_mul(v, &m, g);
    fsyz.add_term_mul(v, &m, gsyz);

    balanced_rem(lc_f, lc_g) == 0
}

/// Classic S-pair construction.
///
/// Returns (spoly, m_f, m_g) where spoly = u * m_f * f - v * m_g * g
/// with (u, v) = syzygy(lc(f), lc(g)), and m_f, m_g are the multiplier
/// monomials from lcm(lt(f), lt(g)).
///
/// The caller uses m_f, m_g to build the syzygy vector.
pub fn cancel_lead_terms(f: &Poly, g: &Poly) -> (Poly, Monomial, Monomial) {
    assert!(!f.is_zero() && !g.is_zero());
    assert_eq!(f.lead_comp(), g.lead_comp());

    let (m_f, m_g) = exponent_syzygy(f.lead_monom(), g.lead_monom());
    let (u, v) = syzygy(f.lead_coeff(), g.lead_coeff());

    // spoly = u * m_f * f + v * m_g * g
    // (syzygy gives u*lc(f) + v*lc(g) = 0, so lead terms cancel)
    let part_f = f.term_mul(u, &m_f);
    let part_g = g.term_mul(v, &m_g);
    let spoly = part_f.add(&part_g);

    (spoly, m_f, m_g)
}

/// GCD S-pair construction over ZZ.
///
/// Uses extended_gcd to combine f and g so the result's lead coefficient
/// is gcd(lc(f), lc(g)). Returns None if u == 0 or v == 0 (no useful combination).
pub fn combine_lead_terms_zz(
    f: &Poly,
    fsyz: &Poly,
    g: &Poly,
    gsyz: &Poly,
) -> Option<(Poly, Poly)> {
    assert!(!f.is_zero() && !g.is_zero());
    assert_eq!(f.lead_comp(), g.lead_comp());

    let (_, u, v) = extended_gcd(f.lead_coeff(), g.lead_coeff());
    if u == 0 || v == 0 {
        return None;
    }

    let (m_f, m_g) = exponent_syzygy(f.lead_monom(), g.lead_monom());

    // result = u * m_f * f + v * m_g * g
    let result = f.term_mul(u, &m_f).add(&g.term_mul(v, &m_g));
    let result_syz = fsyz.term_mul(u, &m_f).add(&gsyz.term_mul(v, &m_g));

    Some((result, result_syz))
}

/// GCD coefficient swap for two polynomials with the same leading monomial.
///
/// Precondition: f and g have the same leading monomial and component.
///
/// After the swap:
/// - new_g has lead coefficient = gcd(lc(old_f), lc(old_g))
/// - new_f has its lead term cancelled (becomes a "remainder" element)
pub fn replace_2by2_zz(f: &mut Poly, fsyz: &mut Poly, g: &mut Poly, gsyz: &mut Poly) {
    assert!(!f.is_zero() && !g.is_zero());

    let lc_f = f.lead_coeff();
    let lc_g = g.lead_coeff();
    let (gd, u, v) = extended_gcd(lc_f, lc_g);

    // new_g = u*f + v*g  (lead coeff becomes gcd)
    let new_g = f.scalar_muled(u).add(&g.scalar_muled(v));
    let new_gsyz = fsyz.scalar_muled(u).add(&gsyz.scalar_muled(v));

    // c = lc(g)/gd, d = -lc(f)/gd
    let c = lc_g / gd;
    let d = -(lc_f / gd);

    // new_f = c*f + d*g  (lead term cancels)
    let new_f = f.scalar_muled(c).add(&g.scalar_muled(d));
    let new_fsyz = fsyz.scalar_muled(c).add(&gsyz.scalar_muled(d));

    *f = new_f;
    *fsyz = new_fsyz;
    *g = new_g;
    *gsyz = new_gsyz;
}

/// Reduce a single tail term of f by g, where g's lead monomial matches
/// a term in f exactly (same monomial and component).
///
/// Uses balanced division to keep coefficients small.
pub fn auto_reduce_tail_zz(f: &mut Poly, fsyz: &mut Poly, g: &Poly, gsyz: &Poly) {
    assert!(!g.is_zero());

    let g_monom = g.lead_monom().clone();
    let g_comp = g.lead_comp();
    let g_lc = g.lead_coeff();

    // Find the matching term in f.
    let b = match f.find_term(&g_monom, g_comp) {
        Some(t) => t.coeff,
        None => return,
    };

    let v = -balanced_div(b, g_lc);
    if v == 0 {
        return;
    }

    // f += v * g (no monomial multiplier — monomials match exactly)
    let one = Monomial::one(g_monom.nvars());
    f.add_term_mul(v, &one, g);
    fsyz.add_term_mul(v, &one, gsyz);
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

    // ===== exponent_syzygy =====

    #[test]
    fn test_exponent_syzygy() {
        let a = m(&[2, 1, 0]);
        let b = m(&[1, 0, 2]);
        let (m1, m2) = exponent_syzygy(&a, &b);
        // lcm = [2,1,2], m1 = [0,0,2], m2 = [1,1,0]
        assert_eq!(m1.exponents(), &[0, 0, 2]);
        assert_eq!(m2.exponents(), &[1, 1, 0]);
        assert_eq!(a.mul(&m1), b.mul(&m2));
    }

    #[test]
    fn test_exponent_syzygy_disjoint() {
        let a = m(&[3, 0, 0]);
        let b = m(&[0, 0, 2]);
        let (m1, m2) = exponent_syzygy(&a, &b);
        assert_eq!(m1.exponents(), &[0, 0, 2]);
        assert_eq!(m2.exponents(), &[3, 0, 0]);
    }

    #[test]
    fn test_exponent_syzygy_equal() {
        let a = m(&[1, 2, 3]);
        let (m1, m2) = exponent_syzygy(&a, &a);
        assert!(m1.is_one());
        assert!(m2.is_one());
    }

    // ===== reduce_lead_term_zz =====

    #[test]
    fn test_reduce_lead_term_exact() {
        // f = 6*x^2 + 3*x, g = 2*x^2 + 1
        // lc(f)=6, lc(g)=2, balanced_div(6,2)=3, v=-3
        // f += -3 * (1) * g = 6x^2+3x + (-3)(2x^2+1) = 3x - 3
        let mut f = p(&[(6, &[2, 0], 0), (3, &[1, 0], 0)]);
        let mut fsyz = Poly::zero();
        let g = p(&[(2, &[2, 0], 0), (1, &[0, 0], 0)]);
        let gsyz = p(&[(1, &[0, 0], 0)]); // e_0

        let fully_cancelled = reduce_lead_term_zz(&mut f, &mut fsyz, &g, &gsyz);
        assert!(fully_cancelled);
        let expected = p(&[(3, &[1, 0], 0), (-3, &[0, 0], 0)]);
        assert_eq!(f, expected);
        // fsyz = 0 + (-3)*1*e_0 = -3*e_0
        assert_eq!(fsyz, p(&[(-3, &[0, 0], 0)]));
    }

    #[test]
    fn test_reduce_lead_term_balanced_remainder() {
        // f = 7*x^2 + x, g = 3*x^2 + 1
        // balanced_div(7,3) = 2 (since 7=2*3+1, and 1 is in (-1.5, 1.5]), v = -2
        // f += -2*(3x^2+1) = 7x^2+x - 6x^2 - 2 = x^2 + x - 2
        // balanced_rem(7,3) = 1 != 0, so not fully cancelled
        let mut f = p(&[(7, &[2, 0], 0), (1, &[1, 0], 0)]);
        let mut fsyz = Poly::zero();
        let g = p(&[(3, &[2, 0], 0), (1, &[0, 0], 0)]);
        let gsyz = p(&[(1, &[0, 0], 0)]);

        let fully_cancelled = reduce_lead_term_zz(&mut f, &mut fsyz, &g, &gsyz);
        assert!(!fully_cancelled);
        let expected = p(&[(1, &[2, 0], 0), (1, &[1, 0], 0), (-2, &[0, 0], 0)]);
        assert_eq!(f, expected);
    }

    #[test]
    fn test_reduce_lead_term_v_zero() {
        // f = 1*x^2, g = 3*x^2  → balanced_div(1,3)=0, v=0 → no reduction
        let mut f = p(&[(1, &[2, 0], 0)]);
        let orig = f.clone();
        let mut fsyz = Poly::zero();
        let g = p(&[(3, &[2, 0], 0), (1, &[0, 0], 0)]);
        let gsyz = p(&[(1, &[0, 0], 0)]);

        let fully_cancelled = reduce_lead_term_zz(&mut f, &mut fsyz, &g, &gsyz);
        assert!(!fully_cancelled);
        assert_eq!(f, orig);
    }

    #[test]
    fn test_reduce_lead_term_with_monomial_quotient() {
        // f = 6*x^2*y + 2, g = 3*x*y + 1
        // monom quotient: x^2*y / x*y = x
        // v = -balanced_div(6, 3) = -2
        // f += -2 * x * (3xy + 1) = 6x^2y + 2 - 6x^2y - 2x = -2x + 2
        let mut f = p(&[(6, &[2, 1], 0), (2, &[0, 0], 0)]);
        let mut fsyz = Poly::zero();
        let g = p(&[(3, &[1, 1], 0), (1, &[0, 0], 0)]);
        let gsyz = p(&[(1, &[0, 0], 0)]);

        let fully_cancelled = reduce_lead_term_zz(&mut f, &mut fsyz, &g, &gsyz);
        assert!(fully_cancelled);
        let expected = p(&[(-2, &[1, 0], 0), (2, &[0, 0], 0)]);
        assert_eq!(f, expected);
    }

    // ===== cancel_lead_terms =====

    #[test]
    fn test_cancel_lead_terms_basic() {
        // f = 3*x^2 + 1, g = 2*x^2 + x
        // syzygy(3, 2) = (2, -3)  [since 3*2 + 2*(-3) = 0]
        // lcm(x^2, x^2) = x^2, m_f = 1, m_g = 1
        // spoly = 2*f + (-3)*g = 6x^2+2 - 6x^2-3x = -3x + 2
        let f = p(&[(3, &[2, 0], 0), (1, &[0, 0], 0)]);
        let g = p(&[(2, &[2, 0], 0), (1, &[1, 0], 0)]);

        let (spoly, m_f, m_g) = cancel_lead_terms(&f, &g);
        assert!(m_f.is_one());
        assert!(m_g.is_one());
        let expected = p(&[(-3, &[1, 0], 0), (2, &[0, 0], 0)]);
        assert_eq!(spoly, expected);
    }

    #[test]
    fn test_cancel_lead_terms_different_monomials() {
        // f = 2*x^2 + 1, g = 3*y^2 + 1
        // lcm(x^2, y^2) = x^2*y^2, m_f = y^2, m_g = x^2
        // syzygy(2, 3) = (3, -2)
        // spoly = 3*y^2*(2x^2+1) + (-2)*x^2*(3y^2+1)
        //       = 6x^2y^2 + 3y^2 - 6x^2y^2 - 2x^2 = -2x^2 + 3y^2
        let f = p(&[(2, &[2, 0], 0), (1, &[0, 0], 0)]);
        let g = p(&[(3, &[0, 2], 0), (1, &[0, 0], 0)]);

        let (spoly, m_f, m_g) = cancel_lead_terms(&f, &g);
        assert_eq!(m_f.exponents(), &[0, 2]);
        assert_eq!(m_g.exponents(), &[2, 0]);
        // grevlex: x^2 > y^2 (same degree, x^2 has smaller last exponent)
        let expected = p(&[(-2, &[2, 0], 0), (3, &[0, 2], 0)]);
        assert_eq!(spoly, expected);
    }

    // ===== combine_lead_terms_zz =====

    #[test]
    fn test_combine_lead_terms_basic() {
        // f = 6*x^2 + 1, g = 4*x^2 + x
        // extended_gcd(6, 4) = (2, 1, -1)  [1*6 + (-1)*4 = 2]
        // Same lead monom, so m_f = m_g = 1
        // result = 1*f + (-1)*g = 6x^2+1 - 4x^2-x = 2x^2 - x + 1
        let f = p(&[(6, &[2, 0], 0), (1, &[0, 0], 0)]);
        let fsyz = p(&[(1, &[0, 0], 0)]); // e_0
        let g = p(&[(4, &[2, 0], 0), (1, &[1, 0], 0)]);
        let gsyz = p(&[(1, &[0, 0], 1)]); // e_1

        let result = combine_lead_terms_zz(&f, &fsyz, &g, &gsyz);
        assert!(result.is_some());
        let (res, res_syz) = result.unwrap();
        assert_eq!(res.lead_coeff(), 2);
        let expected = p(&[(2, &[2, 0], 0), (-1, &[1, 0], 0), (1, &[0, 0], 0)]);
        assert_eq!(res, expected);
        // res_syz = 1*fsyz + (-1)*gsyz = e_0 - e_1
        let expected_syz = p(&[(1, &[0, 0], 0), (-1, &[0, 0], 1)]);
        assert_eq!(res_syz, expected_syz);
    }

    #[test]
    fn test_combine_lead_terms_none_when_u_zero() {
        // If one divides the other exactly, extended_gcd might give u=0 or v=0.
        // extended_gcd(6, 3) = (3, 0, 1) or (3, 1, -1)... let's check.
        // Actually extended_gcd(6, 3): 6 = 2*3 + 0, so g=3, u=0, v=1.
        let f = p(&[(6, &[2, 0], 0), (1, &[0, 0], 0)]);
        let fsyz = Poly::zero();
        let g = p(&[(3, &[2, 0], 0), (1, &[1, 0], 0)]);
        let gsyz = Poly::zero();

        let result = combine_lead_terms_zz(&f, &fsyz, &g, &gsyz);
        assert!(result.is_none());
    }

    // ===== replace_2by2_zz =====

    #[test]
    fn test_replace_2by2_basic() {
        // f = 6*x + 1, g = 4*x + 3 (same lead monomial x)
        // extended_gcd(6, 4) = (2, 1, -1)
        // new_g = 1*(6x+1) + (-1)*(4x+3) = 2x - 2
        // c = 4/2 = 2, d = -6/2 = -3
        // new_f = 2*(6x+1) + (-3)*(4x+3) = 12x+2 - 12x-9 = -7
        let mut f = p(&[(6, &[1, 0], 0), (1, &[0, 0], 0)]);
        let mut fsyz = p(&[(1, &[0, 0], 0)]); // e_0
        let mut g = p(&[(4, &[1, 0], 0), (3, &[0, 0], 0)]);
        let mut gsyz = p(&[(1, &[0, 0], 1)]); // e_1

        replace_2by2_zz(&mut f, &mut fsyz, &mut g, &mut gsyz);

        // new_g lead coeff should be gcd(6,4) = 2
        assert_eq!(g.lead_coeff(), 2);
        assert_eq!(g, p(&[(2, &[1, 0], 0), (-2, &[0, 0], 0)]));
        // new_f lead term should be cancelled (no x term)
        assert_eq!(f, p(&[(-7, &[0, 0], 0)]));
    }

    #[test]
    fn test_replace_2by2_determinant() {
        // The matrix [[u,v],[c,d]] should have determinant ±1.
        let lc_f: i64 = 15;
        let lc_g: i64 = 10;
        let (gd, u, v) = extended_gcd(lc_f, lc_g);
        let c = lc_g / gd;
        let d = -(lc_f / gd);
        // det = u*d - v*c
        let det = u * d - v * c;
        assert!(det == 1 || det == -1, "determinant = {}", det);
    }

    // ===== auto_reduce_tail_zz =====

    #[test]
    fn test_auto_reduce_tail_basic() {
        // f = 5*x^2 + 7*x + 3, g = 3*x + 1
        // g's lead monom is x. Find x in f: coeff = 7.
        // balanced_div(7, 3) = 2 (7 = 2*3 + 1), v = -2
        // f += -2*(3x+1) = 5x^2 + 7x + 3 - 6x - 2 = 5x^2 + x + 1
        let mut f = p(&[(5, &[2, 0], 0), (7, &[1, 0], 0), (3, &[0, 0], 0)]);
        let mut fsyz = Poly::zero();
        let g = p(&[(3, &[1, 0], 0), (1, &[0, 0], 0)]);
        let gsyz = p(&[(1, &[0, 0], 0)]);

        auto_reduce_tail_zz(&mut f, &mut fsyz, &g, &gsyz);

        let expected = p(&[(5, &[2, 0], 0), (1, &[1, 0], 0), (1, &[0, 0], 0)]);
        assert_eq!(f, expected);
    }

    #[test]
    fn test_auto_reduce_tail_no_match() {
        // f = 5*x^2 + 3, g = 3*y + 1
        // g's lead monom is y. No y term in f, so nothing happens.
        let mut f = p(&[(5, &[2, 0], 0), (3, &[0, 0], 0)]);
        let orig = f.clone();
        let mut fsyz = Poly::zero();
        let g = p(&[(3, &[0, 1], 0), (1, &[0, 0], 0)]);
        let gsyz = Poly::zero();

        auto_reduce_tail_zz(&mut f, &mut fsyz, &g, &gsyz);
        assert_eq!(f, orig);
    }

    #[test]
    fn test_auto_reduce_tail_v_zero() {
        // f = 5*x^2 + 1*x, g = 3*x + 1
        // Find x in f: coeff = 1. balanced_div(1, 3) = 0, v = 0, no reduction.
        let mut f = p(&[(5, &[2, 0], 0), (1, &[1, 0], 0)]);
        let orig = f.clone();
        let mut fsyz = Poly::zero();
        let g = p(&[(3, &[1, 0], 0), (1, &[0, 0], 0)]);
        let gsyz = Poly::zero();

        auto_reduce_tail_zz(&mut f, &mut fsyz, &g, &gsyz);
        assert_eq!(f, orig);
    }

    // ===== Syzygy invariant tests =====

    #[test]
    fn test_reduce_lead_term_syzygy_invariant() {
        // Verify: f_new = f_orig + v*m*g, and fsyz tracks this correctly.
        // If we define f_orig - f_new = -v*m*g, then f_new + (-fsyz)*g should
        // reconstruct something consistent.
        //
        // More precisely: if the original system is f = 1*f + 0*g,
        // after reduction f_new = f_orig + v*m*g, fsyz = 0 + v*m*gsyz.
        // So f_new = f_orig + v*m*g, and the relation is:
        //   f_orig = f_new - v*m*g
        //   f_orig = f_new + fsyz_coeff * g  (where fsyz tracks -v*m)

        let f_orig = p(&[(10, &[2, 0], 0), (3, &[1, 0], 0)]);
        let mut f = f_orig.clone();
        let mut fsyz = Poly::zero();
        let g = p(&[(3, &[2, 0], 0), (1, &[0, 0], 0)]);
        let gsyz = p(&[(1, &[0, 0], 0)]); // identity

        reduce_lead_term_zz(&mut f, &mut fsyz, &g, &gsyz);

        // Reconstruct: f_orig should equal f - fsyz_coeff * g
        // fsyz = v * 1 * gsyz = v * e_0, so the coefficient is v.
        // f_orig = f + (-v) * g = f - fsyz_coeff * g
        if !fsyz.is_zero() {
            let v = fsyz.lead_coeff(); // v from the reduction
            let reconstructed = f.add(&g.scalar_muled(-v));
            assert_eq!(reconstructed, f_orig);
        }
    }

    #[test]
    fn test_cancel_lead_terms_cancels() {
        // The S-polynomial should have its leading term cancelled.
        let f = p(&[(3, &[2, 1], 0), (1, &[0, 0], 0)]);
        let g = p(&[(2, &[1, 2], 0), (1, &[1, 0], 0)]);

        let (spoly, _, _) = cancel_lead_terms(&f, &g);

        // The lcm monomial is x^2*y^2. The spoly should not have this monomial.
        if !spoly.is_zero() {
            let lcm_monom = m(&[2, 2]);
            assert!(
                spoly.find_term(&lcm_monom, 0).is_none(),
                "S-poly should not have the lcm monomial"
            );
        }
    }

    #[test]
    fn test_replace_2by2_properties() {
        let mut f = p(&[(15, &[2, 0], 0), (7, &[1, 0], 0), (1, &[0, 0], 0)]);
        let mut fsyz = p(&[(1, &[0, 0], 0)]);
        let mut g = p(&[(10, &[2, 0], 0), (3, &[1, 0], 0), (-2, &[0, 0], 0)]);
        let mut gsyz = p(&[(1, &[0, 0], 1)]);

        let old_lc_f = f.lead_coeff();
        let old_lc_g = g.lead_coeff();

        replace_2by2_zz(&mut f, &mut fsyz, &mut g, &mut gsyz);

        // new_g lead coeff = gcd(15, 10) = 5
        assert_eq!(g.lead_coeff().abs(), crate::zz::gcd(old_lc_f, old_lc_g));
        // new_f should not have x^2 term (lead term cancelled)
        assert!(
            f.is_zero() || f.lead_monom() != &m(&[2, 0]),
            "f's lead term should be cancelled"
        );
    }
}
