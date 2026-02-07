//! Matrix ↔ module generator conversion.
//!
//! An m×n matrix M of polynomials defines a map R^n → R^m.
//! Column j of M becomes a module element: Σ_i M[i][j] * e_i.
//! Syzygies (kernel elements) are converted back to matrix columns.

use crate::poly::{Poly, Term};

/// Convert an m×n matrix (rows × cols) of polynomials to module generators.
///
/// `entries[i][j]` is the polynomial in row i, column j.
/// Column j becomes a module element with comp=i for each row i.
pub fn matrix_to_generators(entries: &[Vec<Poly>], _nvars: usize) -> Vec<Poly> {
    if entries.is_empty() {
        return Vec::new();
    }
    let nrows = entries.len();
    let ncols = entries[0].len();
    assert!(entries.iter().all(|row| row.len() == ncols), "all rows must have same length");

    let mut generators = Vec::with_capacity(ncols);
    for j in 0..ncols {
        let mut terms = Vec::new();
        for i in 0..nrows {
            for t in entries[i][j].terms() {
                terms.push(Term::new(t.coeff, t.monom.clone(), i));
            }
        }
        generators.push(Poly::from_terms(terms));
    }
    generators
}

/// Convert syzygy module elements back to an n×k matrix.
///
/// Each syzygy is a module element with components 0..ngens-1.
/// Returns a matrix where column k is the k-th syzygy, stored as
/// `result[i][k]` = polynomial coefficient of e_i in the k-th syzygy.
///
/// The result has `ngens` rows and `syzygies.len()` columns.
pub fn syzygies_to_matrix(syzygies: &[Poly], ngens: usize, _nvars: usize) -> Vec<Vec<Poly>> {
    let ncols = syzygies.len();
    let mut result: Vec<Vec<Poly>> = (0..ngens)
        .map(|_| (0..ncols).map(|_| Poly::zero()).collect())
        .collect();

    for (k, syz) in syzygies.iter().enumerate() {
        for t in syz.terms() {
            assert!(t.comp < ngens, "syzygy references component {} but ngens={}", t.comp, ngens);
            let ring_term = Term::new(t.coeff, t.monom.clone(), 0);
            result[t.comp][k] = result[t.comp][k].add(&Poly::from_terms(vec![ring_term]));
        }
    }

    result
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
            terms.iter().map(|(c, e)| Term::new(*c, m(e), 0)).collect(),
        )
    }

    #[test]
    fn test_matrix_to_generators_single_row() {
        // 1×2 matrix [x, y] → generators x*e_0 and y*e_0
        let entries = vec![vec![op(&[(1, &[1, 0])]), op(&[(1, &[0, 1])])]];
        let gens = matrix_to_generators(&entries, 2);
        assert_eq!(gens.len(), 2);
        // gen 0 = x in comp 0
        assert_eq!(gens[0].lead_comp(), 0);
        assert_eq!(gens[0].lead_monom(), &m(&[1, 0]));
        // gen 1 = y in comp 0
        assert_eq!(gens[1].lead_comp(), 0);
        assert_eq!(gens[1].lead_monom(), &m(&[0, 1]));
    }

    #[test]
    fn test_matrix_to_generators_2x2() {
        // [[x, y], [y, x]] → gen0 = x*e_0 + y*e_1, gen1 = y*e_0 + x*e_1
        let entries = vec![
            vec![op(&[(1, &[1, 0])]), op(&[(1, &[0, 1])])],
            vec![op(&[(1, &[0, 1])]), op(&[(1, &[1, 0])])],
        ];
        let gens = matrix_to_generators(&entries, 2);
        assert_eq!(gens.len(), 2);
        // gen0 has terms in comp 0 and comp 1
        assert_eq!(gens[0].num_terms(), 2);
    }

    #[test]
    fn test_syzygies_to_matrix() {
        // Syzygy: -y*e_0 + x*e_1
        let syz = Poly::from_terms(vec![
            Term::new(-1, m(&[0, 1]), 0),
            Term::new(1, m(&[1, 0]), 1),
        ]);
        let matrix = syzygies_to_matrix(&[syz], 2, 2);
        assert_eq!(matrix.len(), 2); // 2 rows
        assert_eq!(matrix[0].len(), 1); // 1 column
        // row 0 = -y
        assert_eq!(matrix[0][0], op(&[(-1, &[0, 1])]));
        // row 1 = x
        assert_eq!(matrix[1][0], op(&[(1, &[1, 0])]));
    }

    #[test]
    fn test_roundtrip_single_row() {
        // A 1×2 matrix [x, y]: generators should be pure ring elements.
        let entries = vec![vec![op(&[(1, &[1, 0])]), op(&[(1, &[0, 1])])]];
        let gens = matrix_to_generators(&entries, 2);

        // Create a "syzygy" manually: e_0 - e_1
        let syz = Poly::from_terms(vec![
            Term::new(1, m(&[0, 0]), 0),
            Term::new(-1, m(&[0, 0]), 1),
        ]);
        let matrix = syzygies_to_matrix(&[syz], 2, 2);
        // Row 0 = 1, Row 1 = -1
        assert_eq!(matrix[0][0], op(&[(1, &[0, 0])]));
        assert_eq!(matrix[1][0], op(&[(-1, &[0, 0])]));
    }

    #[test]
    fn test_empty_matrix() {
        let gens = matrix_to_generators(&[], 2);
        assert!(gens.is_empty());
    }
}
