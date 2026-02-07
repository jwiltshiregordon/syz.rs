//! Syzygy computation over ZZ[x1,...,xn].
//!
//! Uses Buchberger GB computation (which collects raw syzygies) and then
//! minimizes and auto-reduces them using Schreyer order.

use crate::gb::gb_compute;
use crate::poly::Poly;
use crate::schreyer::SchreyerOrder;
use crate::zz::{balanced_div, poly_remove_content};

/// Result of a syzygy computation.
pub struct SyzResult {
    /// The Gröbner basis of the input generators.
    pub gb: Vec<Poly>,
    /// The minimized, reduced syzygies of the original generators.
    pub syzygies: Vec<Poly>,
}

/// Compute syzygies of the given generators over ZZ.
///
/// Returns the Gröbner basis and the kernel (syzygies) of the map
/// defined by the generators.
pub fn syz_compute(generators: &[Poly], nvars: usize) -> SyzResult {
    if generators.is_empty() {
        return SyzResult {
            gb: Vec::new(),
            syzygies: Vec::new(),
        };
    }

    // Step 1: Compute GB with syzygy tracking.
    let gb_result = gb_compute(generators, nvars);

    // Step 2: Build Schreyer order from the original generators.
    // Filter out zero generators (gb_compute skips them, but syz vectors reference
    // the original generator indices).
    let nonzero_gens: Vec<&Poly> = generators.iter().filter(|g| !g.is_zero()).collect();
    if nonzero_gens.is_empty() {
        return SyzResult {
            gb: gb_result.gb,
            syzygies: Vec::new(),
        };
    }

    let order = SchreyerOrder::new(
        &nonzero_gens.iter().map(|g| (*g).clone()).collect::<Vec<_>>(),
    );

    // Step 3: Minimize and reduce syzygies.
    let syzygies = minimize_reduce_syzygies(gb_result.syzygies, &order);

    SyzResult {
        gb: gb_result.gb,
        syzygies,
    }
}

/// Minimize and reduce raw syzygies using Schreyer order.
fn minimize_reduce_syzygies(mut raw: Vec<Poly>, order: &SchreyerOrder) -> Vec<Poly> {
    if raw.is_empty() {
        return raw;
    }

    // Step 1: Remove content, normalize sign (positive Schreyer-lead coeff).
    for syz in &mut raw {
        poly_remove_content(syz);
        let lead = order.lead_term(syz);
        if lead.coeff < 0 {
            syz.negate();
        }
    }

    // Step 2: Minimize — reduce each syzygy against others in Schreyer order.
    // Only remove elements that fully reduce to zero.
    // Over ZZ, simple lead-divisibility does not guarantee redundancy.
    let mut syzygies = raw;
    loop {
        let n = syzygies.len();
        let mut removed = false;
        for j in (0..n).rev() {
            // Try to reduce syz[j] fully using the other syzygies.
            let mut f = syzygies[j].clone();
            loop {
                if f.is_zero() {
                    break;
                }
                let f_lead = order.lead_term(&f).clone();
                let mut reduced = false;
                for k in 0..n {
                    if k == j {
                        continue;
                    }
                    let g_lead = order.lead_term(&syzygies[k]).clone();
                    if g_lead.comp == f_lead.comp
                        && g_lead.monom.divides(&f_lead.monom)
                        && f_lead.coeff % g_lead.coeff == 0
                    {
                        let q = f_lead.coeff / g_lead.coeff;
                        let m = f_lead.monom.div(&g_lead.monom);
                        let reducer = syzygies[k].term_mul(q, &m);
                        f = f.add(&reducer.negated());
                        reduced = true;
                        break;
                    }
                }
                if !reduced {
                    break;
                }
            }
            if f.is_zero() {
                syzygies.remove(j);
                removed = true;
            }
        }
        if !removed {
            break;
        }
    }

    // Step 3: Auto-reduce tails using Schreyer order.
    // For each syzygy f, for each other syzygy g, reduce non-lead terms
    // of f that are divisible by g's Schreyer-lead.
    loop {
        let mut changed = false;
        let n = syzygies.len();
        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                let g_lead = order.lead_term(&syzygies[j]).clone();

                // Find a non-lead term of syz[i] that is reducible by g_lead.
                let f_lead = order.lead_term(&syzygies[i]).clone();
                let mut found = None;
                for t in syzygies[i].terms() {
                    // Skip the Schreyer-lead of f.
                    if t.comp == f_lead.comp && t.monom == f_lead.monom {
                        continue;
                    }
                    // Check if g_lead divides this term.
                    if t.comp == g_lead.comp && g_lead.monom.divides(&t.monom) {
                        let v = -balanced_div(t.coeff, g_lead.coeff);
                        if v != 0 {
                            let m = t.monom.div(&g_lead.monom);
                            found = Some((v, m));
                            break;
                        }
                    }
                }

                if let Some((v, m)) = found {
                    let reducer = syzygies[j].term_mul(v, &m);
                    syzygies[i] = syzygies[i].add(&reducer);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Step 4: Re-normalize after reduction.
    for syz in &mut syzygies {
        poly_remove_content(syz);
        let lead = order.lead_term(syz);
        if lead.coeff < 0 {
            syz.negate();
        }
    }

    // Remove any that became zero.
    syzygies.retain(|s| !s.is_zero());

    // Step 5: Sort by Schreyer-lead (ascending Schreyer order).
    syzygies.sort_by(|a, b| {
        let la = order.lead_term(a);
        let lb = order.lead_term(b);
        order.cmp_terms(la, lb)
    });

    syzygies
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::Monomial;
    use crate::poly::{Poly, Term};

    fn m(exps: &[i32]) -> Monomial {
        Monomial::new(exps.to_vec())
    }

    fn op(terms: &[(i64, &[i32])]) -> Poly {
        Poly::from_terms(
            terms
                .iter()
                .map(|(c, e)| Term::new(*c, m(e), 0))
                .collect(),
        )
    }

    fn sp(terms: &[(i64, &[i32], usize)]) -> Poly {
        Poly::from_terms(
            terms
                .iter()
                .map(|(c, e, comp)| Term::new(*c, m(e), *comp))
                .collect(),
        )
    }

    /// Verify that a syzygy is valid: sum of coeff_i * gen_i == 0.
    fn verify_syzygy(syz: &Poly, generators: &[Poly]) {
        let mut sum = Poly::zero();
        for term in syz.terms() {
            assert!(
                term.comp < generators.len(),
                "syzygy references generator {} but only {} generators",
                term.comp,
                generators.len()
            );
            sum = sum.add(&generators[term.comp].term_mul(term.coeff, &term.monom));
        }
        assert!(
            sum.is_zero(),
            "syzygy does not verify: sum = {}",
            sum
        );
    }

    // ===== Basic tests =====

    #[test]
    fn test_syz_empty() {
        let result = syz_compute(&[], 2);
        assert!(result.gb.is_empty());
        assert!(result.syzygies.is_empty());
    }

    #[test]
    fn test_syz_single_generator() {
        let gens = [op(&[(1, &[2, 0]), (1, &[0, 0])])];
        let result = syz_compute(&gens, 2);
        assert_eq!(result.gb.len(), 1);
        assert!(result.syzygies.is_empty());
    }

    #[test]
    fn test_syz_identical_generators() {
        // x, x → syzygy: e_0 - e_1
        let gens = [op(&[(1, &[1, 0])]), op(&[(1, &[1, 0])])];
        let result = syz_compute(&gens, 2);
        assert!(!result.syzygies.is_empty());
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens);
        }
    }

    #[test]
    fn test_syz_scalar_multiples() {
        // 2x, 3x → syzygy: 3*e_0 - 2*e_1
        let gens = [op(&[(2, &[1, 0])]), op(&[(3, &[1, 0])])];
        let result = syz_compute(&gens, 2);
        assert!(!result.syzygies.is_empty());
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens);
        }
    }

    // ===== Verification tests: all syzygies are valid =====

    #[test]
    fn test_syz_coprime_2var() {
        let gens = [
            op(&[(1, &[2, 0]), (1, &[0, 0])]),
            op(&[(1, &[0, 2]), (1, &[0, 0])]),
        ];
        let result = syz_compute(&gens, 2);
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens);
        }
    }

    #[test]
    fn test_syz_monomial_ideal_2var() {
        let gens = [
            op(&[(1, &[2, 0])]),
            op(&[(1, &[1, 1])]),
            op(&[(1, &[0, 2])]),
        ];
        let result = syz_compute(&gens, 2);
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens);
        }
    }

    #[test]
    fn test_syz_twisted_cubic() {
        let gens = [
            op(&[(1, &[2, 0, 0]), (-1, &[0, 1, 1])]),
            op(&[(1, &[1, 1, 0]), (-1, &[0, 0, 2])]),
            op(&[(1, &[0, 2, 0]), (-1, &[1, 0, 1])]),
        ];
        let result = syz_compute(&gens, 3);
        assert!(result.syzygies.len() >= 2, "twisted cubic should have syzygies");
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens);
        }
    }

    #[test]
    fn test_syz_three_linear_2var() {
        let gens = [
            op(&[(6, &[1, 0]), (4, &[0, 1])]),
            op(&[(10, &[1, 0]), (9, &[0, 1])]),
            op(&[(15, &[1, 0]), (2, &[0, 1])]),
        ];
        let result = syz_compute(&gens, 2);
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens);
        }
    }

    #[test]
    fn test_syz_classic_2var() {
        let gens = [
            op(&[(1, &[2, 0]), (-1, &[0, 1])]),
            op(&[(1, &[1, 1]), (-1, &[1, 0])]),
        ];
        let result = syz_compute(&gens, 2);
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens);
        }
    }

    // ================================================================
    // Multi-row oracle tests
    // Generated by: echo 'load "tests/oracle/syz_multirow.m2"' | M2 --silent --no-readline
    //
    // Each test builds a 2×3 matrix over ZZ[x,y], converts to module
    // generators via matrix_to_generators, runs syz_compute, and
    // compares syzygies against M2 output (exact match + verification).
    // ================================================================

    use crate::matrix::matrix_to_generators;

    /// Build generators from a 2×3 matrix given as [[row0], [row1]].
    fn gens_2x3(row0: &[Poly], row1: &[Poly]) -> Vec<Poly> {
        let entries = vec![row0.to_vec(), row1.to_vec()];
        matrix_to_generators(&entries, 2)
    }

    #[test]
    fn test_oracle_multirow_identity_like() {
        // M = [[1, 0, x], [0, 1, y]]
        let gens = gens_2x3(
            &[op(&[(1, &[0, 0])]), op(&[]),              op(&[(1, &[1, 0])])],
            &[op(&[]),              op(&[(1, &[0, 0])]), op(&[(1, &[0, 1])])],
        );
        let result = syz_compute(&gens, 2);
        assert_eq!(result.syzygies.len(), 1, "IDENTITY_LIKE: expected 1 syzygy");
        // M2: [(1, {1, 0}, 0), (1, {0, 1}, 1), (-1, {0, 0}, 2)]
        assert_eq!(result.syzygies[0], sp(&[
            (1, &[1, 0], 0), (1, &[0, 1], 1), (-1, &[0, 0], 2),
        ]));
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens);
        }
    }

    #[test]
    fn test_oracle_multirow_linear_2x3() {
        // M = [[x, y, x+y], [y, x, x-y]]
        let gens = gens_2x3(
            &[op(&[(1, &[1, 0])]), op(&[(1, &[0, 1])]), op(&[(1, &[1, 0]), (1, &[0, 1])])],
            &[op(&[(1, &[0, 1])]), op(&[(1, &[1, 0])]), op(&[(1, &[1, 0]), (-1, &[0, 1])])],
        );
        let result = syz_compute(&gens, 2);
        assert_eq!(result.syzygies.len(), 1, "LINEAR_2x3: expected 1 syzygy");
        // M2: [(-1, {2, 0}, 0), (-1, {0, 2}, 0), (-1, {2, 0}, 1), (2, {1, 1}, 1), (1, {0, 2}, 1), (1, {2, 0}, 2), (-1, {0, 2}, 2)]
        assert_eq!(result.syzygies[0], sp(&[
            (-1, &[2, 0], 0), (-1, &[0, 2], 0),
            (-1, &[2, 0], 1), (2, &[1, 1], 1), (1, &[0, 2], 1),
            (1, &[2, 0], 2), (-1, &[0, 2], 2),
        ]));
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens);
        }
    }

    #[test]
    fn test_oracle_multirow_mixed_degree_2x3() {
        // M = [[x^2, y, 1], [x, xy, y^2]]
        let gens = gens_2x3(
            &[op(&[(1, &[2, 0])]), op(&[(1, &[0, 1])]), op(&[(1, &[0, 0])])],
            &[op(&[(1, &[1, 0])]), op(&[(1, &[1, 1])]), op(&[(1, &[0, 2])])],
        );
        let result = syz_compute(&gens, 2);
        assert_eq!(result.syzygies.len(), 1, "MIXED_DEGREE_2x3: expected 1 syzygy");
        // M2: [(-1, {0, 3}, 0), (1, {1, 1}, 0), (1, {2, 2}, 1), (-1, {1, 0}, 1), (-1, {3, 1}, 2), (1, {1, 1}, 2)]
        assert_eq!(result.syzygies[0], sp(&[
            (-1, &[0, 3], 0), (1, &[1, 1], 0),
            (1, &[2, 2], 1), (-1, &[1, 0], 1),
            (-1, &[3, 1], 2), (1, &[1, 1], 2),
        ]));
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens);
        }
    }

    #[test]
    fn test_oracle_multirow_zero_column() {
        // M = [[x, 0, y], [y, 0, x]]
        let gens = gens_2x3(
            &[op(&[(1, &[1, 0])]), op(&[]), op(&[(1, &[0, 1])])],
            &[op(&[(1, &[0, 1])]), op(&[]), op(&[(1, &[1, 0])])],
        );
        let result = syz_compute(&gens, 2);
        assert_eq!(result.syzygies.len(), 1, "ZERO_COLUMN: expected 1 syzygy");
        // M2: [(1, {0, 0}, 1)]
        assert_eq!(result.syzygies[0], sp(&[
            (1, &[0, 0], 1),
        ]));
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens);
        }
    }

    #[test]
    fn test_oracle_multirow_rank_1() {
        // M = [[x, 2x, 3x], [y, 2y, 3y]]
        let gens = gens_2x3(
            &[op(&[(1, &[1, 0])]), op(&[(2, &[1, 0])]), op(&[(3, &[1, 0])])],
            &[op(&[(1, &[0, 1])]), op(&[(2, &[0, 1])]), op(&[(3, &[0, 1])])],
        );
        // Debug: manually inspect minimization
        let gb_result = crate::gb::gb_compute(&gens, 2);
        let nonzero_gens: Vec<&Poly> = gens.iter().filter(|g| !g.is_zero()).collect();
        let order = crate::schreyer::SchreyerOrder::new(
            &nonzero_gens.iter().map(|g| (*g).clone()).collect::<Vec<_>>(),
        );
        eprintln!("Raw syzygies:");
        for (i, s) in gb_result.syzygies.iter().enumerate() {
            let lead = order.lead_term(s);
            eprintln!("  raw syz {}: {:?}", i, s);
            eprintln!("    Schreyer lead: {:?}", lead);
        }
        let result = syz_compute(&gens, 2);
        eprintln!("Final syzygies: {}", result.syzygies.len());
        for (i, s) in result.syzygies.iter().enumerate() {
            eprintln!("  final syz {}: {:?}", i, s);
        }
        assert_eq!(result.syzygies.len(), 2, "RANK_1: expected 2 syzygies");
        // M2 syz 0: [(-2, {0, 0}, 0), (1, {0, 0}, 1)]
        assert_eq!(result.syzygies[0], sp(&[
            (-2, &[0, 0], 0), (1, &[0, 0], 1),
        ]));
        // M2 syz 1: [(-3, {0, 0}, 0), (1, {0, 0}, 2)]
        assert_eq!(result.syzygies[1], sp(&[
            (-3, &[0, 0], 0), (1, &[0, 0], 2),
        ]));
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens);
        }
    }

    #[test]
    fn test_oracle_multirow_coefficients_2x3() {
        // M = [[2x, 3y, 5], [3, 2x, 7y]]
        let gens = gens_2x3(
            &[op(&[(2, &[1, 0])]), op(&[(3, &[0, 1])]), op(&[(5, &[0, 0])])],
            &[op(&[(3, &[0, 0])]), op(&[(2, &[1, 0])]), op(&[(7, &[0, 1])])],
        );
        let result = syz_compute(&gens, 2);
        // M2 returns 3 syzygies. Verify count and that all are valid.
        assert_eq!(result.syzygies.len(), 3, "COEFFICIENTS_2x3: expected 3 syzygies");
        // M2 syz 0: [(-210, {0, 2}, 0), (100, {1, 0}, 0), (140, {1, 1}, 1), (-150, {0, 0}, 1), (-40, {2, 0}, 2), (90, {0, 1}, 2)]
        assert_eq!(result.syzygies[0], sp(&[
            (-210, &[0, 2], 0), (100, &[1, 0], 0),
            (140, &[1, 1], 1), (-150, &[0, 0], 1),
            (-40, &[2, 0], 2), (90, &[0, 1], 2),
        ]));
        // M2 syz 1: [(-21, {0, 2}, 0), (10, {1, 0}, 0), (14, {1, 1}, 1), (-15, {0, 0}, 1), (-4, {2, 0}, 2), (9, {0, 1}, 2)]
        assert_eq!(result.syzygies[1], sp(&[
            (-21, &[0, 2], 0), (10, &[1, 0], 0),
            (14, &[1, 1], 1), (-15, &[0, 0], 1),
            (-4, &[2, 0], 2), (9, &[0, 1], 2),
        ]));
        // M2 syz 2: same as syz 1
        assert_eq!(result.syzygies[2], sp(&[
            (-21, &[0, 2], 0), (10, &[1, 0], 0),
            (14, &[1, 1], 1), (-15, &[0, 0], 1),
            (-4, &[2, 0], 2), (9, &[0, 1], 2),
        ]));
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens);
        }
    }
}
