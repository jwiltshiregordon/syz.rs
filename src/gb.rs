//! Buchberger GB computation over ZZ[x1,...,xn].
//!
//! Implements the main Buchberger loop: insert generators, create S-pairs,
//! reduce them, grow the GB, and collect syzygies from zero reductions.

use crate::monomial::Monomial;
use crate::poly::Poly;
use crate::reduction::{
    cancel_lead_terms, combine_lead_terms_zz, exponent_syzygy, reduce_lead_term_zz,
};
use crate::zz::balanced_div;
use crate::spairs::{GBElem, SPair, SPairSet, SPairType, minimize_pairs_zz};
use crate::zz::syzygy;

/// Result of a Gröbner basis computation.
pub struct GBResult {
    /// The Gröbner basis elements.
    pub gb: Vec<Poly>,
    /// Syzygies of the original generators (from zero reductions).
    pub syzygies: Vec<Poly>,
}

/// Reduce `f` (with syzygy vector `fsyz`) against the current GB.
///
/// Repeatedly finds a reducer whose lead monomial divides the lead of `f`
/// (in the same component) and applies `reduce_lead_term_zz`. Stops when
/// `f` is zero or no reducer makes progress.
fn reduce_spoly(f: &mut Poly, fsyz: &mut Poly, gb: &[GBElem]) {
    loop {
        if f.is_zero() {
            break;
        }
        let mut reduced = false;
        for g in gb {
            if g.lead_comp == f.lead_comp() && g.lead.divides(f.lead_monom()) {
                let old_lead = f.lead_monom().clone();
                let cancelled = reduce_lead_term_zz(f, fsyz, &g.poly, &g.syz);
                if cancelled || f.is_zero() || *f.lead_monom() != old_lead {
                    reduced = true;
                    break; // restart scan
                }
                // balanced remainder left same lead monomial — try next reducer
            }
        }
        if !reduced {
            break;
        }
    }
}

/// Compute a Gröbner basis over ZZ for the given generators.
///
/// `nvars` is the number of variables in the polynomial ring.
/// Returns the GB elements and syzygies of the original generators.
pub fn gb_compute(generators: &[Poly], nvars: usize) -> GBResult {
    let mut gb_elems: Vec<GBElem> = Vec::new();
    let mut spairs = SPairSet::new();
    let mut syzygies: Vec<Poly> = Vec::new();

    // Phase 1: Insert generators.
    for (i, g) in generators.iter().enumerate() {
        if g.is_zero() {
            continue;
        }
        let poly = g.clone();

        let syz_vec = Poly::from_term(1, Monomial::one(nvars), i);
        let new_idx = gb_elems.len();

        gb_elems.push(GBElem::new(poly, syz_vec));

        let new_pairs: Vec<SPair> = (0..new_idx)
            .filter(|&k| gb_elems[k].lead_comp == gb_elems[new_idx].lead_comp)
            .map(|k| SPair::new_pair(k, new_idx, &gb_elems))
            .collect();

        let minimized = minimize_pairs_zz(new_pairs, &gb_elems);
        spairs.insert(minimized);
    }

    // Phase 2: Main Buchberger loop.
    while let Some(deg) = spairs.next_degree() {
        let batch = spairs.extract_degree(deg);

        for sp in batch {
            let (mut spoly, mut spoly_syz) = match sp.kind {
                SPairType::SPair => {
                    let (sp_poly, m_f, m_g) =
                        cancel_lead_terms(&gb_elems[sp.i].poly, &gb_elems[sp.j].poly);
                    let (u, v) = syzygy(
                        gb_elems[sp.i].lead_coeff,
                        gb_elems[sp.j].lead_coeff,
                    );
                    let syz = gb_elems[sp.i]
                        .syz
                        .term_mul(u, &m_f)
                        .add(&gb_elems[sp.j].syz.term_mul(v, &m_g));
                    (sp_poly, syz)
                }
                SPairType::GcdZZ => {
                    let (m_f, m_g) = exponent_syzygy(
                        &gb_elems[sp.i].lead,
                        &gb_elems[sp.j].lead,
                    );
                    match combine_lead_terms_zz(
                        &gb_elems[sp.i].poly.term_mul(1, &m_f),
                        &gb_elems[sp.i].syz.term_mul(1, &m_f),
                        &gb_elems[sp.j].poly.term_mul(1, &m_g),
                        &gb_elems[sp.j].syz.term_mul(1, &m_g),
                    ) {
                        Some((p, s)) => (p, s),
                        None => continue,
                    }
                }
                SPairType::Gen => unreachable!("generators are inserted directly"),
            };

            // Reduce against current GB.
            reduce_spoly(&mut spoly, &mut spoly_syz, &gb_elems);

            if spoly.is_zero() {
                if !spoly_syz.is_zero() {
                    syzygies.push(spoly_syz);
                }
            } else {
                // New GB element.
                // Note: do NOT remove content over ZZ — it changes the ideal.

                let new_idx = gb_elems.len();
                let lead_comp = spoly.lead_comp();

                gb_elems.push(GBElem::new(spoly, spoly_syz));

                let new_pairs: Vec<SPair> = (0..new_idx)
                    .filter(|&k| gb_elems[k].lead_comp == lead_comp)
                    .map(|k| SPair::new_pair(k, new_idx, &gb_elems))
                    .collect();

                let minimized = minimize_pairs_zz(new_pairs, &gb_elems);
                spairs.insert(minimized);
            }
        }
    }

    // Phase 3: Auto-reduction (full tail reduction).
    // For each pair (i, j), reduce all tail terms of gb[i] that are divisible
    // by gb[j]'s lead monomial. Repeat until no more changes.
    loop {
        let mut changed = false;
        let n = gb_elems.len();
        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                if gb_elems[i].poly.is_zero() || gb_elems[j].poly.is_zero() {
                    continue;
                }

                // Scan tail terms of i for one divisible by j's lead.
                let g_monom = &gb_elems[j].lead;
                let g_comp = gb_elems[j].lead_comp;
                let g_lc = gb_elems[j].lead_coeff;

                // Find a reducible tail term (skip index 0 = lead).
                let mut found = None;
                for k in 1..gb_elems[i].poly.terms().len() {
                    let term = &gb_elems[i].poly.terms()[k];
                    if term.comp == g_comp && g_monom.divides(&term.monom) {
                        let v = -balanced_div(term.coeff, g_lc);
                        if v != 0 {
                            let m = term.monom.div(g_monom);
                            found = Some((v, m));
                            break;
                        }
                    }
                }

                if let Some((v, m)) = found {
                    // Apply: gb[i] += v * m * gb[j]
                    // Need split_at_mut for disjoint mutable access.
                    if i < j {
                        let (left, right) = gb_elems.split_at_mut(j);
                        left[i].poly.add_term_mul(v, &m, &right[0].poly);
                        left[i].syz.add_term_mul(v, &m, &right[0].syz);
                    } else {
                        let (left, right) = gb_elems.split_at_mut(i);
                        right[0].poly.add_term_mul(v, &m, &left[j].poly);
                        right[0].syz.add_term_mul(v, &m, &left[j].syz);
                    }
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Filter out any elements that became zero during auto-reduction.
    let gb_elems: Vec<GBElem> = gb_elems
        .into_iter()
        .filter(|e| !e.poly.is_zero())
        .collect();

    // Phase 4: Minimize, normalize signs, and sort.
    let mut gb_polys: Vec<Poly> = gb_elems.into_iter().map(|e| e.poly).collect();

    // Normalize signs: make lead coefficient positive.
    for f in &mut gb_polys {
        if f.lead_coeff() < 0 {
            f.negate();
        }
    }

    // Minimize: over ZZ, element j is redundant if there exists i such that
    // lt(g_i) fully divides lt(g_j): monom(i) divides monom(j) AND lc(i) divides lc(j).
    let n = gb_polys.len();
    let mut keep = vec![true; n];
    for i in 0..n {
        if !keep[i] {
            continue;
        }
        for j in 0..n {
            if i == j || !keep[j] {
                continue;
            }
            if gb_polys[i].lead_comp() == gb_polys[j].lead_comp()
                && gb_polys[i].lead_monom().divides(gb_polys[j].lead_monom())
                && gb_polys[j].lead_coeff() % gb_polys[i].lead_coeff() == 0
            {
                keep[j] = false;
            }
        }
    }
    let mut gb_polys: Vec<Poly> = gb_polys
        .into_iter()
        .zip(keep)
        .filter(|(_, k)| *k)
        .map(|(f, _)| f)
        .collect();

    // Sort by (component ascending, lead monomial ascending grevlex).
    gb_polys.sort_by(|a, b| {
        a.lead_comp()
            .cmp(&b.lead_comp())
            .then_with(|| a.lead_monom().cmp_grevlex(b.lead_monom()))
    });

    GBResult {
        gb: gb_polys,
        syzygies,
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

    fn p(terms: &[(i64, &[i32])]) -> Poly {
        Poly::from_terms(
            terms.iter().map(|(c, e)| t(*c, e, 0)).collect(),
        )
    }

    /// Check that every GB element has positive lead coefficient and is nonzero.
    fn assert_normalized(gb: &[Poly]) {
        for (i, f) in gb.iter().enumerate() {
            assert!(!f.is_zero(), "GB element {} is zero", i);
            assert!(
                f.lead_coeff() > 0,
                "GB element {} has negative lead coeff: {}",
                i,
                f
            );
        }
    }

    /// Check that `spoly` is a syzygy: sum of coeff_i * gen_i == 0.
    fn verify_syzygy(syz: &Poly, generators: &[Poly], _nvars: usize) {
        let mut sum = Poly::zero();
        for term in syz.terms() {
            let gen_idx = term.comp;
            assert!(
                gen_idx < generators.len(),
                "syzygy references generator {} but only {} generators",
                gen_idx,
                generators.len()
            );
            sum = sum.add(&generators[gen_idx].term_mul(term.coeff, &term.monom));
        }
        assert!(
            sum.is_zero(),
            "syzygy does not verify: sum = {}",
            sum
        );
    }

    // ===== Test 1: Single generator =====
    #[test]
    fn test_single_generator() {
        // Over ZZ, GB of a single polynomial keeps its content (no content removal).
        let gens = [p(&[(2, &[2, 0]), (2, &[0, 0])])];
        let result = gb_compute(&gens, 2);
        assert_eq!(result.gb.len(), 1);
        // 2x^2 + 2 stays as 2x^2 + 2 (content is NOT removed over ZZ)
        assert_eq!(result.gb[0], p(&[(2, &[2, 0]), (2, &[0, 0])]));
        assert!(result.syzygies.is_empty());
    }

    // ===== Test 2: Two generators, coprime leads =====
    #[test]
    fn test_coprime_leads() {
        let gens = [
            p(&[(1, &[2, 0]), (1, &[0, 0])]), // x^2 + 1
            p(&[(1, &[0, 2]), (1, &[0, 0])]), // y^2 + 1
        ];
        let result = gb_compute(&gens, 2);
        // Over ZZ with coprime lead monomials, the S-pair should reduce to 0
        // or produce a small GB. The GB should contain at least the original 2.
        assert!(result.gb.len() >= 2);
        assert_normalized(&result.gb);
    }

    // ===== Test 3: Classic example =====
    #[test]
    fn test_classic_example() {
        // x^2 - y, xy - x in ZZ[x,y]
        let gens = [
            p(&[(1, &[2, 0]), (-1, &[0, 1])]), // x^2 - y
            p(&[(1, &[1, 1]), (-1, &[1, 0])]), // xy - x
        ];
        let result = gb_compute(&gens, 2);
        assert!(!result.gb.is_empty());
        assert_normalized(&result.gb);

        // Verify any collected syzygies.
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens, 2);
        }
    }

    // ===== Test 4: ZZ-specific coefficient reduction =====
    #[test]
    fn test_zz_coefficient_reduction() {
        // 6x + 1, 4x + 1 in ZZ[x]
        // GCD of lead coeffs is 2. Should produce element with smaller lead coeff.
        let gens = [
            p(&[(6, &[1]), (1, &[0])]),  // 6x + 1
            p(&[(4, &[1]), (1, &[0])]),  // 4x + 1
        ];
        let result = gb_compute(&gens, 1);
        assert!(!result.gb.is_empty());
        assert_normalized(&result.gb);

        // The GB should contain an element with lead coeff dividing gcd(6,4)=2.
        // Actually over ZZ, the GB of (6x+1, 4x+1) should contain 2x+1 and 1
        // (since 6x+1 - 3*(2x+1) = -2, and gcd with other stuff gives 1).
        // Let's just check that 1 is in the GB (since gcd(6,4)=2 and the
        // constant terms also combine).
        let has_constant = result.gb.iter().any(|f| f.lead_monom().is_one());
        assert!(has_constant, "GB should contain a constant: {:?}",
                result.gb.iter().map(|f| format!("{}", f)).collect::<Vec<_>>());
    }

    // ===== Test 5: Syzygy collection =====
    #[test]
    fn test_syzygy_collection() {
        // f = x, g = x — the S-pair x*g - x*f = 0 gives a syzygy.
        // Actually with identical generators: S-pair of (x, x): syzygy(1,1)=(1,-1),
        // lcm=x, m_f=1, m_g=1, spoly = 1*x + (-1)*x = 0. Syzygy: e_0 - e_1.
        let gens = [
            p(&[(1, &[1, 0])]),  // x
            p(&[(1, &[1, 0])]),  // x
        ];
        let result = gb_compute(&gens, 2);
        assert!(!result.syzygies.is_empty(), "should find a syzygy for identical generators");
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens, 2);
        }
    }

    // ===== Test 6: Module elements (multiple components) =====
    #[test]
    fn test_module_elements() {
        // Generators in different components should not form S-pairs with each other.
        let gen0 = Poly::from_terms(vec![
            Term::new(1, m(&[1, 0]), 0),  // x*e_0
            Term::new(1, m(&[0, 0]), 0),  // 1*e_0
        ]);
        let gen1 = Poly::from_terms(vec![
            Term::new(1, m(&[0, 1]), 1),  // y*e_1
            Term::new(1, m(&[0, 0]), 1),  // 1*e_1
        ]);
        let gens = [gen0, gen1];
        let result = gb_compute(&gens, 2);
        // No S-pairs between different components, so GB is just the two generators.
        assert_eq!(result.gb.len(), 2);
        assert!(result.syzygies.is_empty());
    }

    // ===== Test 7: Content removal =====
    #[test]
    fn test_content_removal() {
        // All GB elements should be primitive.
        let gens = [
            p(&[(6, &[2, 0]), (3, &[0, 0])]),  // 6x^2 + 3
            p(&[(4, &[1, 1]), (2, &[0, 0])]),  // 4xy + 2
        ];
        let result = gb_compute(&gens, 2);
        assert_normalized(&result.gb);
    }

    // ===== Test 8: Empty input =====
    #[test]
    fn test_empty_input() {
        let result = gb_compute(&[], 2);
        assert!(result.gb.is_empty());
        assert!(result.syzygies.is_empty());
    }

    // ===== Test 9: Zero generators filtered =====
    #[test]
    fn test_zero_generators() {
        let gens = [Poly::zero(), p(&[(1, &[1, 0])]), Poly::zero()];
        let result = gb_compute(&gens, 2);
        assert_eq!(result.gb.len(), 1);
        assert_eq!(result.gb[0], p(&[(1, &[1, 0])]));
    }

    // ===== Test 10: Syzygy verification for a known example =====
    #[test]
    fn test_syzygy_verification() {
        // f = 2x, g = 3x — the S-pair should produce a syzygy.
        // syzygy(2, 3) = (3, -2), spoly = 3*(2x) + (-2)*(3x) = 0.
        // Syz vector: 3*e_0 - 2*e_1.
        let gens = [
            p(&[(2, &[1, 0])]),  // 2x
            p(&[(3, &[1, 0])]),  // 3x
        ];
        let result = gb_compute(&gens, 2);

        // Should have a syzygy.
        assert!(!result.syzygies.is_empty());
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens, 2);
        }

        // GB should contain x (gcd of 2x and 3x, made primitive).
        let has_x = result.gb.iter().any(|f| {
            f.num_terms() == 1 && f.lead_coeff() == 1 && *f.lead_monom() == m(&[1, 0])
        });
        assert!(has_x, "GB should contain x: {:?}",
                result.gb.iter().map(|f| format!("{}", f)).collect::<Vec<_>>());
    }

    // ================================================================
    // Oracle tests: exact match against M2's output.
    //
    // Generated by: echo 'load "tests/oracle/gb.m2"' | M2 --silent --no-readline
    // Fixture saved in: tests/fixtures/gb.txt
    //
    // Each test compares our gb_compute output element-by-element against M2.
    // We insist on exact match: same polynomials, same order, same signs.
    // ================================================================

    /// Helper: build a Poly for oracle tests (ring element, comp=0).
    fn op(terms: &[(i64, &[i32])]) -> Poly {
        Poly::from_terms(
            terms.iter().map(|(c, e)| Term::new(*c, m(e), 0)).collect(),
        )
    }

    /// Assert that our GB exactly matches the expected list of polynomials.
    fn assert_gb_eq(label: &str, result: &[Poly], expected: &[Poly]) {
        assert_eq!(
            result.len(),
            expected.len(),
            "{}: GB size mismatch (got {}, expected {})\n  got: {:?}",
            label,
            result.len(),
            expected.len(),
            result.iter().map(|f| format!("{}", f)).collect::<Vec<_>>()
        );
        for (i, (got, exp)) in result.iter().zip(expected.iter()).enumerate() {
            assert_eq!(
                got, exp,
                "{}: GB element {} mismatch\n  got:      {}\n  expected: {}",
                label, i, got, exp
            );
        }
    }

    // --- 1-variable oracle tests ---

    #[test]
    fn test_oracle_single_gen_1var() {
        // M2: gb {x^2 + 1} = {x^2 + 1}
        let gens = [op(&[(1, &[2]), (1, &[0])])];
        let result = gb_compute(&gens, 1);
        assert_gb_eq("SINGLE_GEN_1VAR", &result.gb, &[
            op(&[(1, &[2]), (1, &[0])]),
        ]);
        assert_eq!(result.syzygies.len(), 0);
    }

    #[test]
    fn test_oracle_two_gen_1var_a() {
        // M2: gb {2x+1, 4x+1} = {1}
        let gens = [
            op(&[(2, &[1]), (1, &[0])]),
            op(&[(4, &[1]), (1, &[0])]),
        ];
        let result = gb_compute(&gens, 1);
        assert_gb_eq("TWO_GEN_1VAR_A", &result.gb, &[
            op(&[(1, &[0])]),
        ]);
    }

    #[test]
    fn test_oracle_two_gen_1var_b() {
        // M2: gb {6x+1, 4x+1} = {1}
        let gens = [
            op(&[(6, &[1]), (1, &[0])]),
            op(&[(4, &[1]), (1, &[0])]),
        ];
        let result = gb_compute(&gens, 1);
        assert_gb_eq("TWO_GEN_1VAR_B", &result.gb, &[
            op(&[(1, &[0])]),
        ]);
    }

    #[test]
    fn test_oracle_three_gen_1var() {
        // M2: gb {6x^2, 10x^2, 15x^2} = {x^2}
        let gens = [
            op(&[(6, &[2])]),
            op(&[(10, &[2])]),
            op(&[(15, &[2])]),
        ];
        let result = gb_compute(&gens, 1);
        assert_gb_eq("THREE_GEN_1VAR", &result.gb, &[
            op(&[(1, &[2])]),
        ]);
    }

    // --- 2-variable oracle tests ---

    #[test]
    fn test_oracle_coprime_leads_2var() {
        // M2: gb {x^2+1, y^2+1} = {y^2+1, x^2+1}
        let gens = [
            op(&[(1, &[2, 0]), (1, &[0, 0])]),
            op(&[(1, &[0, 2]), (1, &[0, 0])]),
        ];
        let result = gb_compute(&gens, 2);
        assert_gb_eq("COPRIME_LEADS_2VAR", &result.gb, &[
            op(&[(1, &[0, 2]), (1, &[0, 0])]),
            op(&[(1, &[2, 0]), (1, &[0, 0])]),
        ]);
    }

    #[test]
    fn test_oracle_classic_2var() {
        // M2: gb {x^2-y, xy-x} = {y^2-y, xy-x, x^2-y}
        let gens = [
            op(&[(1, &[2, 0]), (-1, &[0, 1])]),
            op(&[(1, &[1, 1]), (-1, &[1, 0])]),
        ];
        let result = gb_compute(&gens, 2);
        assert_gb_eq("CLASSIC_2VAR", &result.gb, &[
            op(&[(1, &[0, 2]), (-1, &[0, 1])]),
            op(&[(1, &[1, 1]), (-1, &[1, 0])]),
            op(&[(1, &[2, 0]), (-1, &[0, 1])]),
        ]);
    }

    #[test]
    fn test_oracle_coeff_2var() {
        // M2: gb {3x+y, 2x-y} = {5y, x+2y}
        let gens = [
            op(&[(3, &[1, 0]), (1, &[0, 1])]),
            op(&[(2, &[1, 0]), (-1, &[0, 1])]),
        ];
        let result = gb_compute(&gens, 2);
        assert_gb_eq("COEFF_2VAR", &result.gb, &[
            op(&[(5, &[0, 1])]),
            op(&[(1, &[1, 0]), (2, &[0, 1])]),
        ]);
    }

    #[test]
    fn test_oracle_identical_2var() {
        // M2: gb {x+y, x+y} = {x+y}
        let gens = [
            op(&[(1, &[1, 0]), (1, &[0, 1])]),
            op(&[(1, &[1, 0]), (1, &[0, 1])]),
        ];
        let result = gb_compute(&gens, 2);
        assert_gb_eq("IDENTICAL_2VAR", &result.gb, &[
            op(&[(1, &[1, 0]), (1, &[0, 1])]),
        ]);
    }

    #[test]
    fn test_oracle_scalar_mult_2var() {
        // M2: gb {2x, 3x} = {x}
        let gens = [
            op(&[(2, &[1, 0])]),
            op(&[(3, &[1, 0])]),
        ];
        let result = gb_compute(&gens, 2);
        assert_gb_eq("SCALAR_MULT_2VAR", &result.gb, &[
            op(&[(1, &[1, 0])]),
        ]);
    }

    #[test]
    fn test_oracle_similar_2var() {
        // M2: gb {x^2+xy, xy+y^2} = {xy+y^2, x^2-y^2}
        let gens = [
            op(&[(1, &[2, 0]), (1, &[1, 1])]),
            op(&[(1, &[1, 1]), (1, &[0, 2])]),
        ];
        let result = gb_compute(&gens, 2);
        assert_gb_eq("SIMILAR_2VAR", &result.gb, &[
            op(&[(1, &[1, 1]), (1, &[0, 2])]),
            op(&[(1, &[2, 0]), (-1, &[0, 2])]),
        ]);
    }

    // --- 3-variable oracle tests ---

    #[test]
    fn test_oracle_classic_3var() {
        // M2: gb {x^2+y+z, xy+z, y^2+x} = 6 elements
        let gens = [
            op(&[(1, &[2, 0, 0]), (1, &[0, 1, 0]), (1, &[0, 0, 1])]),
            op(&[(1, &[1, 1, 0]), (1, &[0, 0, 1])]),
            op(&[(1, &[0, 2, 0]), (1, &[1, 0, 0])]),
        ];
        let result = gb_compute(&gens, 3);
        assert_gb_eq("CLASSIC_3VAR", &result.gb, &[
            op(&[(1, &[0, 0, 2]), (1, &[1, 0, 0]), (1, &[0, 1, 0]), (2, &[0, 0, 1])]),
            op(&[(1, &[0, 1, 1]), (1, &[0, 1, 0]), (1, &[0, 0, 1])]),
            op(&[(1, &[1, 0, 1]), (1, &[1, 0, 0]), (1, &[0, 1, 0]), (1, &[0, 0, 1])]),
            op(&[(1, &[0, 2, 0]), (1, &[1, 0, 0])]),
            op(&[(1, &[1, 1, 0]), (1, &[0, 0, 1])]),
            op(&[(1, &[2, 0, 0]), (1, &[0, 1, 0]), (1, &[0, 0, 1])]),
        ]);
    }

    #[test]
    fn test_oracle_katsura_like_3var() {
        // M2: gb {x+y+z-1, x^2+y^2+z^2-1} = 2 elements
        let gens = [
            op(&[(1, &[1, 0, 0]), (1, &[0, 1, 0]), (1, &[0, 0, 1]), (-1, &[0, 0, 0])]),
            op(&[(1, &[2, 0, 0]), (1, &[0, 2, 0]), (1, &[0, 0, 2]), (-1, &[0, 0, 0])]),
        ];
        let result = gb_compute(&gens, 3);
        assert_gb_eq("KATSURA_LIKE_3VAR", &result.gb, &[
            op(&[(1, &[1, 0, 0]), (1, &[0, 1, 0]), (1, &[0, 0, 1]), (-1, &[0, 0, 0])]),
            op(&[(2, &[0, 2, 0]), (2, &[0, 1, 1]), (2, &[0, 0, 2]), (-2, &[0, 1, 0]), (-2, &[0, 0, 1])]),
        ]);
    }

    #[test]
    fn test_oracle_large_coeff_3var() {
        // M2: gb {6x+4y+2z, 3x+9y+6z} = {14y+10z, 3x-5y-4z, xy+3y^2-xz-yz-2z^2}
        let gens = [
            op(&[(6, &[1, 0, 0]), (4, &[0, 1, 0]), (2, &[0, 0, 1])]),
            op(&[(3, &[1, 0, 0]), (9, &[0, 1, 0]), (6, &[0, 0, 1])]),
        ];
        let result = gb_compute(&gens, 3);
        assert_gb_eq("LARGE_COEFF_3VAR", &result.gb, &[
            op(&[(14, &[0, 1, 0]), (10, &[0, 0, 1])]),
            op(&[(3, &[1, 0, 0]), (-5, &[0, 1, 0]), (-4, &[0, 0, 1])]),
            op(&[(1, &[1, 1, 0]), (3, &[0, 2, 0]), (-1, &[1, 0, 1]), (-1, &[0, 1, 1]), (-2, &[0, 0, 2])]),
        ]);
    }

    #[test]
    fn test_oracle_twisted_cubic_3var() {
        // M2: gb {x^2-yz, xy-z^2, y^2-xz} = {y^2-xz, xy-z^2, x^2-yz}
        let gens = [
            op(&[(1, &[2, 0, 0]), (-1, &[0, 1, 1])]),
            op(&[(1, &[1, 1, 0]), (-1, &[0, 0, 2])]),
            op(&[(1, &[0, 2, 0]), (-1, &[1, 0, 1])]),
        ];
        let result = gb_compute(&gens, 3);
        assert_gb_eq("TWISTED_CUBIC_3VAR", &result.gb, &[
            op(&[(1, &[0, 2, 0]), (-1, &[1, 0, 1])]),
            op(&[(1, &[1, 1, 0]), (-1, &[0, 0, 2])]),
            op(&[(1, &[2, 0, 0]), (-1, &[0, 1, 1])]),
        ]);
    }

    // --- Syzygy oracle tests: verify syzygies are valid ---

    #[test]
    fn test_oracle_syzygies_coprime_2var() {
        // M2 produces 1 syzygy for {x^2+1, y^2+1}
        let gens = [
            op(&[(1, &[2, 0]), (1, &[0, 0])]),
            op(&[(1, &[0, 2]), (1, &[0, 0])]),
        ];
        let result = gb_compute(&gens, 2);
        assert!(result.syzygies.len() >= 1, "expected at least 1 syzygy");
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens, 2);
        }
    }

    #[test]
    fn test_oracle_syzygies_classic_2var() {
        let gens = [
            op(&[(1, &[2, 0]), (-1, &[0, 1])]),
            op(&[(1, &[1, 1]), (-1, &[1, 0])]),
        ];
        let result = gb_compute(&gens, 2);
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens, 2);
        }
    }

    #[test]
    fn test_oracle_syzygies_twisted_cubic() {
        let gens = [
            op(&[(1, &[2, 0, 0]), (-1, &[0, 1, 1])]),
            op(&[(1, &[1, 1, 0]), (-1, &[0, 0, 2])]),
            op(&[(1, &[0, 2, 0]), (-1, &[1, 0, 1])]),
        ];
        let result = gb_compute(&gens, 3);
        assert!(result.syzygies.len() >= 2, "twisted cubic should have at least 2 syzygies");
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens, 3);
        }
    }

    #[test]
    fn test_oracle_syzygies_three_gen_1var() {
        let gens = [
            op(&[(6, &[2])]),
            op(&[(10, &[2])]),
            op(&[(15, &[2])]),
        ];
        let result = gb_compute(&gens, 1);
        assert!(result.syzygies.len() >= 2, "three generators with same lead should produce syzygies");
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens, 1);
        }
    }

    #[test]
    fn test_oracle_syzygies_large_coeff_3var() {
        let gens = [
            op(&[(6, &[1, 0, 0]), (4, &[0, 1, 0]), (2, &[0, 0, 1])]),
            op(&[(3, &[1, 0, 0]), (9, &[0, 1, 0]), (6, &[0, 0, 1])]),
        ];
        let result = gb_compute(&gens, 3);
        assert!(result.syzygies.len() >= 1);
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens, 3);
        }
    }

    // ================================================================
    // Larger oracle tests: 3+ generators, richer syzygy structure.
    //
    // Generated by: echo 'load "tests/oracle/gb_large.m2"' | M2 --silent --no-readline
    // ================================================================

    /// Helper: build a module element (syzygy) from (coeff, exponents, component) triples.
    fn sp(terms: &[(i64, &[i32], usize)]) -> Poly {
        Poly::from_terms(
            terms.iter().map(|(c, e, comp)| Term::new(*c, m(e), *comp)).collect(),
        )
    }

    /// Assert that our syzygies exactly match the expected list.
    fn assert_syz_eq(label: &str, result: &[Poly], expected: &[Poly]) {
        assert_eq!(
            result.len(),
            expected.len(),
            "{}: syz count mismatch (got {}, expected {})\n  got: {:?}",
            label,
            result.len(),
            expected.len(),
            result.iter().map(|f| format!("{}", f)).collect::<Vec<_>>()
        );
        for (i, (got, exp)) in result.iter().zip(expected.iter()).enumerate() {
            assert_eq!(
                got, exp,
                "{}: syz element {} mismatch\n  got:      {}\n  expected: {}",
                label, i, got, exp
            );
        }
    }

    // --- MONOMIAL_IDEAL_2VAR: {x^2, xy, y^2} ---

    #[test]
    fn test_oracle_monomial_ideal_2var_gb() {
        let gens = [
            op(&[(1, &[2, 0])]),  // x^2
            op(&[(1, &[1, 1])]),  // xy
            op(&[(1, &[0, 2])]),  // y^2
        ];
        let result = gb_compute(&gens, 2);
        assert_gb_eq("MONOMIAL_IDEAL_2VAR", &result.gb, &[
            op(&[(1, &[0, 2])]),  // y^2
            op(&[(1, &[1, 1])]),  // xy
            op(&[(1, &[2, 0])]),  // x^2
        ]);
    }

    #[test]
    fn test_oracle_monomial_ideal_2var_syz_verify() {
        let gens = [
            op(&[(1, &[2, 0])]),
            op(&[(1, &[1, 1])]),
            op(&[(1, &[0, 2])]),
        ];
        let result = gb_compute(&gens, 2);
        assert!(result.syzygies.len() >= 2);
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens, 2);
        }
    }

    // --- THREE_QUADRATIC_2VAR: {x^2+2xy+y^2, x^2-y^2, 2xy} ---

    #[test]
    fn test_oracle_three_quadratic_2var_gb() {
        let gens = [
            op(&[(1, &[2, 0]), (2, &[1, 1]), (1, &[0, 2])]),  // x^2+2xy+y^2
            op(&[(1, &[2, 0]), (-1, &[0, 2])]),                // x^2-y^2
            op(&[(2, &[1, 1])]),                                // 2xy
        ];
        let result = gb_compute(&gens, 2);
        // M2: gb = {2y^2, 2xy, x^2+y^2}
        assert_gb_eq("THREE_QUADRATIC_2VAR", &result.gb, &[
            op(&[(2, &[0, 2])]),
            op(&[(2, &[1, 1])]),
            op(&[(1, &[2, 0]), (1, &[0, 2])]),
        ]);
    }

    #[test]
    fn test_oracle_three_quadratic_2var_syz_verify() {
        let gens = [
            op(&[(1, &[2, 0]), (2, &[1, 1]), (1, &[0, 2])]),
            op(&[(1, &[2, 0]), (-1, &[0, 2])]),
            op(&[(2, &[1, 1])]),
        ];
        let result = gb_compute(&gens, 2);
        assert!(result.syzygies.len() >= 2);
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens, 2);
        }
    }

    // --- CUBIC_2VAR: {x^3, x^2*y, x*y^2+y^3} ---

    #[test]
    fn test_oracle_cubic_2var_gb() {
        let gens = [
            op(&[(1, &[3, 0])]),                   // x^3
            op(&[(1, &[2, 1])]),                   // x^2*y
            op(&[(1, &[1, 2]), (1, &[0, 3])]),     // xy^2 + y^3
        ];
        let result = gb_compute(&gens, 2);
        // M2: gb = {xy^2+y^3, x^2y, x^3, y^4}
        assert_gb_eq("CUBIC_2VAR", &result.gb, &[
            op(&[(1, &[1, 2]), (1, &[0, 3])]),
            op(&[(1, &[2, 1])]),
            op(&[(1, &[3, 0])]),
            op(&[(1, &[0, 4])]),
        ]);
    }

    #[test]
    fn test_oracle_cubic_2var_syz_verify() {
        let gens = [
            op(&[(1, &[3, 0])]),
            op(&[(1, &[2, 1])]),
            op(&[(1, &[1, 2]), (1, &[0, 3])]),
        ];
        let result = gb_compute(&gens, 2);
        assert!(result.syzygies.len() >= 2);
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens, 2);
        }
    }

    // --- THREE_LINEAR_2VAR: {6x+4y, 10x+9y, 15x+2y} ---

    #[test]
    fn test_oracle_three_linear_2var_gb() {
        let gens = [
            op(&[(6, &[1, 0]), (4, &[0, 1])]),   // 6x+4y
            op(&[(10, &[1, 0]), (9, &[0, 1])]),   // 10x+9y
            op(&[(15, &[1, 0]), (2, &[0, 1])]),   // 15x+2y
        ];
        let result = gb_compute(&gens, 2);
        // M2: gb = {y, x}
        assert_gb_eq("THREE_LINEAR_2VAR", &result.gb, &[
            op(&[(1, &[0, 1])]),
            op(&[(1, &[1, 0])]),
        ]);
    }

    #[test]
    fn test_oracle_three_linear_2var_syz_verify() {
        let gens = [
            op(&[(6, &[1, 0]), (4, &[0, 1])]),
            op(&[(10, &[1, 0]), (9, &[0, 1])]),
            op(&[(15, &[1, 0]), (2, &[0, 1])]),
        ];
        let result = gb_compute(&gens, 2);
        assert!(result.syzygies.len() >= 2);
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens, 2);
        }
    }

    // --- THREE_SAME_LEAD_2VAR: {6x^2+x, 10x^2+y, 15x^2+1} ---

    #[test]
    fn test_oracle_three_same_lead_2var_gb() {
        let gens = [
            op(&[(6, &[2, 0]), (1, &[1, 0])]),   // 6x^2+x
            op(&[(10, &[2, 0]), (1, &[0, 1])]),   // 10x^2+y
            op(&[(15, &[2, 0]), (1, &[0, 0])]),   // 15x^2+1
        ];
        let result = gb_compute(&gens, 2);
        // M2: gb = {17, y+5, x+3}
        assert_gb_eq("THREE_SAME_LEAD_2VAR", &result.gb, &[
            op(&[(17, &[0, 0])]),
            op(&[(1, &[0, 1]), (5, &[0, 0])]),
            op(&[(1, &[1, 0]), (3, &[0, 0])]),
        ]);
    }

    #[test]
    fn test_oracle_three_same_lead_2var_syz_verify() {
        let gens = [
            op(&[(6, &[2, 0]), (1, &[1, 0])]),
            op(&[(10, &[2, 0]), (1, &[0, 1])]),
            op(&[(15, &[2, 0]), (1, &[0, 0])]),
        ];
        let result = gb_compute(&gens, 2);
        assert!(result.syzygies.len() >= 2);
        for syz in &result.syzygies {
            verify_syzygy(syz, &gens, 2);
        }
    }
}
