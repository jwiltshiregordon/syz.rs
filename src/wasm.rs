//! WASM bindings for syzygy computation.

use wasm_bindgen::prelude::*;

use crate::matrix::{matrix_to_generators, syzygies_to_matrix};
use crate::parser::PolyParser;
use crate::poly::Poly;
use crate::syz::syz_compute;

/// Compute syz(M) for a matrix M of polynomials over ZZ[vars].
///
/// # Arguments
/// - `var_names`: comma-separated variable names (e.g. "x, y, z")
/// - `nrows`: number of rows in the matrix
/// - `ncols`: number of columns in the matrix
/// - `entries`: semicolon-separated polynomials in row-major order
///
/// # Returns
/// A JSON string with fields:
/// - `gb`: array of GB polynomial strings
/// - `syz`: 2D array of syzygy matrix entries (ngens × nsyz)
/// - `error`: error message if parsing failed
#[wasm_bindgen]
pub fn compute_syz(var_names: &str, nrows: usize, ncols: usize, entries: &str) -> String {
    match compute_syz_inner(var_names, nrows, ncols, entries) {
        Ok(result) => result,
        Err(e) => format!("{{\"error\":{}}}", json_string(&e)),
    }
}

fn compute_syz_inner(
    var_names: &str,
    nrows: usize,
    ncols: usize,
    entries: &str,
) -> Result<String, String> {
    // Parse variable names.
    let vars: Vec<String> = var_names
        .split(',')
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect();
    if vars.is_empty() {
        return Err("no variables specified".to_string());
    }
    let nvars = vars.len();
    let parser = PolyParser::new(vars);

    // Parse matrix entries.
    let entry_strs: Vec<&str> = entries.split(';').collect();
    if entry_strs.len() != nrows * ncols {
        return Err(format!(
            "expected {} entries ({}x{}), got {}",
            nrows * ncols,
            nrows,
            ncols,
            entry_strs.len()
        ));
    }

    let mut matrix: Vec<Vec<Poly>> = Vec::with_capacity(nrows);
    for i in 0..nrows {
        let mut row = Vec::with_capacity(ncols);
        for j in 0..ncols {
            let s = entry_strs[i * ncols + j].trim();
            let poly = parser.parse(s).map_err(|e| format!("entry [{},{}]: {}", i, j, e))?;
            row.push(poly);
        }
        matrix.push(row);
    }

    // Convert to module generators and compute.
    let generators = matrix_to_generators(&matrix, nvars);
    let ngens = generators.len();
    let result = syz_compute(&generators, nvars);

    // Format GB.
    let gb_strs: Vec<String> = result
        .gb
        .iter()
        .map(|p| {
            if nrows == 1 {
                // Single row: format as ring elements.
                parser.format_poly(p)
            } else {
                // Multi-row: format as module elements.
                let rows = parser.format_module_element(p, nrows);
                format!("[{}]", rows.join(", "))
            }
        })
        .collect();

    // Format syzygies as matrix.
    let syz_matrix = syzygies_to_matrix(&result.syzygies, ngens, nvars);
    let nsyz = result.syzygies.len();

    let mut syz_strs: Vec<Vec<String>> = Vec::new();
    for i in 0..ngens {
        let mut row_strs = Vec::new();
        for k in 0..nsyz {
            row_strs.push(parser.format_poly(&syz_matrix[i][k]));
        }
        syz_strs.push(row_strs);
    }

    // Build JSON response.
    let mut json = String::from("{");

    json.push_str("\"gb\":[");
    for (i, s) in gb_strs.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        json.push_str(&json_string(s));
    }
    json.push_str("],");

    json.push_str("\"syz\":[");
    for (i, row) in syz_strs.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        json.push('[');
        for (j, s) in row.iter().enumerate() {
            if j > 0 {
                json.push(',');
            }
            json.push_str(&json_string(s));
        }
        json.push(']');
    }
    json.push_str("],");

    json.push_str(&format!("\"ngens\":{},", ngens));
    json.push_str(&format!("\"nsyz\":{}", nsyz));

    json.push('}');
    Ok(json)
}

fn json_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compute_syz_basic() {
        let result = compute_syz("x, y", 1, 2, "x; y");
        assert!(!result.contains("error"), "unexpected error: {}", result);
        assert!(result.contains("\"gb\""));
        assert!(result.contains("\"syz\""));
    }

    #[test]
    fn test_compute_syz_error() {
        let result = compute_syz("x, y", 1, 2, "x");
        assert!(result.contains("error"));
    }

    #[test]
    fn test_compute_syz_single_gen() {
        let result = compute_syz("x, y", 1, 1, "x^2 + 1");
        assert!(!result.contains("error"), "unexpected error: {}", result);
        assert!(result.contains("\"nsyz\":0"));
    }

    #[test]
    fn test_compute_syz_monomials() {
        // syz(x^2, xy, y^2) should have 2 syzygies
        let result = compute_syz("x, y", 1, 3, "x^2; x*y; y^2");
        assert!(!result.contains("error"), "unexpected error: {}", result);
        assert!(result.contains("\"nsyz\":2"), "expected 2 syzygies: {}", result);
    }
}
