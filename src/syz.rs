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

    // Step 2: Minimize — remove syzygy j if syzygy i's Schreyer-lead divides j's.
    let n = raw.len();
    let mut keep = vec![true; n];
    for i in 0..n {
        if !keep[i] {
            continue;
        }
        let lead_i = order.lead_term(&raw[i]).clone();
        for j in 0..n {
            if i == j || !keep[j] {
                continue;
            }
            let lead_j = order.lead_term(&raw[j]);
            if order.divides(&lead_i, lead_j) {
                keep[j] = false;
            }
        }
    }

    let mut syzygies: Vec<Poly> = raw
        .into_iter()
        .zip(keep)
        .filter(|(_, k)| *k)
        .map(|(s, _)| s)
        .collect();

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
}
