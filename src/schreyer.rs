//! Schreyer order for syzygy computation.
//!
//! Given generators gen_0, ..., gen_{n-1}, the Schreyer order on the syzygy
//! module compares terms m*e_i vs n*e_j by "lifting" them:
//!   lift(m, i) = (m * lt_monom(gen_i), lt_comp(gen_i))
//! and comparing the lifted terms in the original module order
//! (component ascending, grevlex descending), with tiebreak by generator index.

use std::cmp::Ordering;

use crate::monomial::Monomial;
use crate::poly::{Poly, Term};

/// Schreyer order induced by a set of generators.
pub struct SchreyerOrder {
    /// Lead monomial of each generator.
    gen_lead_monoms: Vec<Monomial>,
    /// Lead component of each generator.
    gen_lead_comps: Vec<usize>,
}

impl SchreyerOrder {
    /// Build a Schreyer order from generators.
    /// Each generator must be nonzero.
    pub fn new(generators: &[Poly]) -> Self {
        let gen_lead_monoms: Vec<Monomial> = generators
            .iter()
            .map(|g| g.lead_monom().clone())
            .collect();
        let gen_lead_comps: Vec<usize> = generators
            .iter()
            .map(|g| g.lead_comp())
            .collect();
        SchreyerOrder {
            gen_lead_monoms,
            gen_lead_comps,
        }
    }

    /// Compare two syzygy terms in Schreyer order.
    ///
    /// Term a has monomial `a.monom` and component `a.comp` (= generator index i).
    /// Term b has monomial `b.monom` and component `b.comp` (= generator index j).
    ///
    /// Lift: (a.monom * lt_monom(gen_i), lt_comp(gen_i)) vs
    ///       (b.monom * lt_monom(gen_j), lt_comp(gen_j))
    /// Compare in module order (comp ascending, grevlex descending).
    /// Tiebreak: larger generator index is greater (i.e., compare i vs j ascending).
    pub fn cmp_terms(&self, a: &Term, b: &Term) -> Ordering {
        let lifted_monom_a = a.monom.mul(&self.gen_lead_monoms[a.comp]);
        let lifted_monom_b = b.monom.mul(&self.gen_lead_monoms[b.comp]);
        let lifted_comp_a = self.gen_lead_comps[a.comp];
        let lifted_comp_b = self.gen_lead_comps[b.comp];

        // Module order: component ascending, then grevlex descending.
        match lifted_comp_a.cmp(&lifted_comp_b) {
            Ordering::Equal => {
                match lifted_monom_a.cmp_grevlex(&lifted_monom_b) {
                    // Reversed: larger grevlex monomial comes first in module order,
                    // so it is "less" in our sorted order. But for Schreyer comparison
                    // we want "Greater" to mean "is the lead direction" (bigger in order).
                    // In the standard module order, (comp asc, grevlex desc) means
                    // "smaller comp or larger grevlex" is the lead. So the comparison
                    // for "which is greater in Schreyer order" matches the module order.
                    Ordering::Equal => {
                        // Tiebreak by generator index: smaller index is greater
                        // (matches M2 convention where earlier generators have priority).
                        a.comp.cmp(&b.comp).reverse()
                    }
                    grevlex_ord => grevlex_ord,
                }
            }
            comp_ord => comp_ord.reverse(),
        }
    }

    /// Find the Schreyer-lead term of a syzygy (the max term in Schreyer order).
    ///
    /// Note: the Schreyer-lead may not be the first term in standard poly order.
    pub fn lead_term<'a>(&self, syz: &'a Poly) -> &'a Term {
        assert!(!syz.is_zero(), "lead_term of zero syzygy");
        syz.terms()
            .iter()
            .max_by(|a, b| self.cmp_terms(a, b))
            .unwrap()
    }

    /// Check if term a's Schreyer-position divides term b's.
    ///
    /// For Schreyer minimization over ZZ: a divides b means
    /// a.monom divides b.monom AND a.comp == b.comp AND |a.coeff| divides |b.coeff|.
    pub fn divides(&self, a: &Term, b: &Term) -> bool {
        a.comp == b.comp
            && a.monom.divides(&b.monom)
            && b.coeff % a.coeff == 0
    }

    /// Number of generators.
    pub fn ngens(&self) -> usize {
        self.gen_lead_monoms.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::Monomial;
    use crate::poly::{Poly, Term};

    fn m(exps: &[i32]) -> Monomial {
        Monomial::new(exps.to_vec())
    }

    fn t(coeff: i64, exps: &[i32], comp: usize) -> Term {
        Term::new(coeff, m(exps), comp)
    }

    fn p(terms: &[(i64, &[i32], usize)]) -> Poly {
        Poly::from_terms(
            terms.iter().map(|(c, e, comp)| t(*c, e, *comp)).collect(),
        )
    }

    fn op(terms: &[(i64, &[i32])]) -> Poly {
        Poly::from_terms(
            terms.iter().map(|(c, e)| Term::new(*c, m(e), 0)).collect(),
        )
    }

    #[test]
    fn test_schreyer_order_basic() {
        // Generators: g0 = x^2, g1 = xy, g2 = y^2
        // Lead terms: x^2*e_0, xy*e_0, y^2*e_0
        let gens = [
            op(&[(1, &[2, 0])]),
            op(&[(1, &[1, 1])]),
            op(&[(1, &[0, 2])]),
        ];
        let order = SchreyerOrder::new(&gens);
        assert_eq!(order.ngens(), 3);
    }

    #[test]
    fn test_schreyer_cmp_different_lifted_degree() {
        // g0 = x^2, g1 = xy. Both comp=0.
        // Term a = y*e_0: lifted = y*x^2 = x^2*y (deg 3)
        // Term b = 1*e_1: lifted = 1*xy = xy (deg 2)
        // deg 3 > deg 2, so a > b in grevlex, a > b in Schreyer order.
        let gens = [
            op(&[(1, &[2, 0])]),
            op(&[(1, &[1, 1])]),
        ];
        let order = SchreyerOrder::new(&gens);

        let a = t(1, &[0, 1], 0); // y*e_0
        let b = t(1, &[0, 0], 1); // 1*e_1
        assert_eq!(order.cmp_terms(&a, &b), Ordering::Greater);
    }

    #[test]
    fn test_schreyer_cmp_same_lifted_monom_tiebreak() {
        // g0 = x^2, g1 = xy. Both comp=0.
        // Term a = y*e_0: lifted = y*x^2 = x^2*y (deg 3, comp 0)
        // Term b = x*e_1: lifted = x*xy = x^2*y (deg 3, comp 0)
        // Same lifted monom and comp → tiebreak by generator index.
        // a.comp=0 < b.comp=1, reversed → a > b.
        let gens = [
            op(&[(1, &[2, 0])]),
            op(&[(1, &[1, 1])]),
        ];
        let order = SchreyerOrder::new(&gens);

        let a = t(1, &[0, 1], 0); // y*e_0
        let b = t(1, &[1, 0], 1); // x*e_1
        assert_eq!(order.cmp_terms(&a, &b), Ordering::Greater);
    }

    #[test]
    fn test_schreyer_lead_term() {
        // g0 = x^2, g1 = xy, g2 = y^2.
        // Syzygy: -y*e_0 + x*e_1 (standard syzygy of x^2 and xy).
        // In Schreyer order:
        //   -y*e_0 lifts to y*x^2 = x^2*y
        //   x*e_1 lifts to x*xy = x^2*y
        //   Tiebreak: comp 0 < comp 1, reversed → e_0 term wins.
        let gens = [
            op(&[(1, &[2, 0])]),
            op(&[(1, &[1, 1])]),
            op(&[(1, &[0, 2])]),
        ];
        let order = SchreyerOrder::new(&gens);

        let syz = p(&[(-1, &[0, 1], 0), (1, &[1, 0], 1)]);
        let lead = order.lead_term(&syz);
        assert_eq!(lead.comp, 0);
        assert_eq!(lead.monom, m(&[0, 1]));
    }

    #[test]
    fn test_schreyer_divides() {
        let a = t(2, &[1, 0], 0);
        let b = t(6, &[2, 1], 0);
        let gens = [op(&[(1, &[2, 0])])];
        let order = SchreyerOrder::new(&gens);

        // Same comp, monom divides, coeff divides
        assert!(order.divides(&a, &b));

        // Different comp
        let c = t(6, &[2, 1], 1);
        assert!(!order.divides(&a, &c));

        // Coeff doesn't divide
        let d = t(5, &[2, 1], 0);
        assert!(!order.divides(&a, &d));
    }

    #[test]
    fn test_schreyer_order_module_elements() {
        // Generators in different components.
        // g0 = x*e_0, g1 = y*e_1
        let gen0 = Poly::from_terms(vec![Term::new(1, m(&[1, 0]), 0)]);
        let gen1 = Poly::from_terms(vec![Term::new(1, m(&[0, 1]), 1)]);
        let gens = [gen0, gen1];
        let order = SchreyerOrder::new(&gens);

        // Term a = 1*e_0: lifted = 1*x = x, comp=0
        // Term b = 1*e_1: lifted = 1*y = y, comp=1
        // Different components: comp 0 < comp 1, reversed → a > b.
        let a = t(1, &[0, 0], 0);
        let b = t(1, &[0, 0], 1);
        assert_eq!(order.cmp_terms(&a, &b), Ordering::Greater);
    }
}
