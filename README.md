# m2-port

A faithful Rust port of a targeted subset of the [Macaulay2](https://macaulay2.com) engine, focused on computing syzygies of matrices over polynomial rings of the form **ZZ[x1, ..., xn]**. Output matches M2's `syz` exactly — same polynomials, same order, same signs.

## Goal

Extract and reimplement the minimal codepath required to run the Macaulay2 command:

```
syz M
```

where `M` is an m×n matrix with entries in a polynomial ring `ZZ[vars]`. A 1×n matrix encodes an ideal, but the general case is an m×n matrix defining a map R^n → R^m. This involves porting:

- The default Groebner basis algorithm from the M2 engine
- Matrices, polynomials, and monomials for the ring `ZZ[x1, ..., xn]`
- The syzygy computation that sits on top of the GB machinery

The scope is deliberately narrow — we are not porting Macaulay2 in general, only the engine code reachable from `syz` over `ZZ[vars]`. In particular, we don't want to implement general modules, just "free modules".

## How syz works in M2

The `syz` command computes the kernel of a matrix `M` — i.e., a matrix whose columns generate all relations among the columns of `M`. Under the hood, this falls out of the Groebner basis computation: when an S-pair reduces to zero, the combination that produced it is a syzygy. The engine tracks these as it goes.

The call chain looks like:

1. **M2 language layer** (`m2/gb.m2`): `syz` calls `rawGBSyzygies` on a GB computation object.
2. **Engine interface** (`e/interface/groebner.cpp`): `rawGBSyzygies(Computation *C)` extracts the collected syzygies.
3. **GB algorithm** (`e/gb-default.cpp`): class `gbA` — a Buchberger algorithm that collects syzygies during S-pair reduction.

## Key M2 engine files

All paths relative to `M2/Macaulay2/e/` (the engine directory).

### Core algorithm

- **`gb-default.hpp/cpp`** — The default GB algorithm (class `gbA`). Buchberger's algorithm with S-pair strategies, sugar degree tracking, and special handling for ZZ coefficients. This is the main thing to port.

### Data structures

- **`gbring.hpp`** — The `gbvector` and `POLY` types used during GB computation. A `gbvector` is a linked list of terms, each with a coefficient, a monomial, and a component index (for free modules). A `POLY` pairs a polynomial `f` with its syzygy representation `fsyz`, so the engine can track syzygies as it reduces.

- **`monoid.hpp`** — Monomial representation and ordering. Monomials are `int*` arrays encoding exponents, a component index, and weight vector values (for term order comparison).

- **`ringelem.hpp`** / **`polyring.hpp`** — Polynomial representation in the ring layer. An `Nterm` is a linked-list node with a coefficient and monomial. We only need the `ZZ[vars]` case.

- **`freemod.hpp`** — Free modules. A `FreeModule` is a list of generator degrees plus an optional Schreyer order. Schreyer orders are induced monomial orderings used to make syzygy computation work correctly.

- **`matrix.hpp`** — Matrices as sparse column vectors over a pair of free modules (source and target).

- **`schorder.hpp`** — Schreyer order encoding. When computing syzygies, the syzygy module gets an induced term order from the GB of the previous level. This is what makes iterated syzygy computation (i.e., free resolutions) efficient.

### Interface

- **`interface/groebner.cpp`** — The C++ entry points (`rawGB`, `rawGBSyzygies`, etc.) that wire the M2 language layer to the engine.

## M2 test files

Useful for generating test cases:

- `M2/Macaulay2/tests/normal/syz1.m2`
- `M2/Macaulay2/tests/normal/syz2.m2`
- `M2/Macaulay2/tests/normal/syz-schreyer-order.m2`

## Status

Functional. The full `syz` pipeline is implemented (GB computation, syzygy collection, Schreyer minimization/reduction) with 157+ tests passing, including oracle tests that verify exact match against M2. A WASM-powered website is available for interactive use.
