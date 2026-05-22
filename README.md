# Euler's polyhedron formula in Lean 4

Formalization of **V - E + F = 2** for connected planar graphs, built on
Lean 4 + Mathlib. Uses the `CombinatorialMap` structure from mathlib4
PR #16074, alongside an inductive `PlanarGraph` type for structural results.

No `sorry`. CI on every commit.

## Selected results

| Result | Description |
|---|---|
| `euler_formula` | V + F = E + 2 for any `PlanarGraph` |
| `platonic_classification` | The five Platonic solids (Wiedijk #38) |
| `petersen_not_planar`, `heawood_not_planar` | Non-planarity via girth bounds (girth hypothesis is assumed, not proved) |
| `girth_planarity_bound` | Edge bound from girth; implies K₅ and K₃,₃ cases |
| `edge_count_eq` | \|E\| = \|D\|/2 for any fixed-point-free involution |
| `eulerChar_of_spherical` | `IsSpherical → IsPlanar` via the CMap bridge |
| `isSpherical_iff_isPlanar` | Equivalence between the two internal planarity notions |
| `euler_via_vanStaudt` | Jordan-free Euler for any CMap satisfying the partition |
| `torusCMap_fails_vanStaudt` | Torus as explicit non-planar counterexample |

## Status

The combinatorial side is complete: inductive `PlanarGraph`, nine parametric
families, Platonic solid classification, non-planarity of K₅ and K₃,₃
(formally via `SimpleGraph`), concrete CMap witnesses for triangle through
octahedron, and a Jordan-free arithmetic derivation for explicit maps.

Petersen and Heawood are now formally defined as `SimpleGraph (Fin n)` instances
with machine-verified edge counts, following the same pattern as K₅. Their
non-planarity uses a girth bound: any planar embedding would force a face-size
inequality that contradicts Euler — the girth itself is not formally proved.

What remains: constructing the spanning-tree partition algorithmically for
arbitrary CMaps (currently verified by `native_decide` on concrete instances),
and connecting to topological planarity in ℝ², which requires either the
Jordan curve theorem or the full Walkup reduction (`Hypermap.lean`).

## Related work

| System | Approach |
|---|---|
| HOL Light (Harrison, 2005) | Full topological JCT proof |
| Coq / Rocq (Gonthier 2005, Dufourd 2008) | Hypermap combinatorial Jordan |
| Isabelle (Bauer & Nipkow 2002) | Triangulations |
| Mathlib4 PR #16074 | Combinatorial map structure (open) |

## Build

    lake build

Lean 4.29.1 + Mathlib.
