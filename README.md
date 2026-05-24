# Euler's polyhedron formula in Lean 4

Formalization of **V - E + F = 2** for connected planar graphs, built on
Lean 4 + Mathlib. Uses the `CombinatorialMap` structure from mathlib4
PR #16074, alongside an inductive `PlanarGraph` type for structural results.

No `sorry`. CI on every commit.

## Status and limitations

This repository develops the **combinatorial side** of planarity: Euler's
formula is proved on an inductive `PlanarGraph` type whose constructors
(`point`, `addLeaf`, `addEdge`) are exactly the operations that preserve
`V - E + F`. Concrete witnesses (`triangle`, `k4`, `cube_witness`,
`octahedron_witness`, `dodecahedron_planar_witness`,
`icosahedron_planar_witness`) verify that classical examples sit inside
this type.

The bridge to **topological planarity in ℝ²** is in progress in
`Hypermap.lean` (Walkup reduction). The Jordan-curve route is not pursued
here; the Jordan-free arithmetic derivation lives in `Completeness.lean`
(`euler_via_vanStaudt`) and is currently verified by `native_decide` on
explicit CMaps, with the torus as a non-planar counterexample
(`torusCMap_fails_vanStaudt`).

What this repository **does not** claim: a full proof that any graph
admitting a topological embedding in ℝ² is a `PlanarGraph` in our sense.
That direction requires either the Jordan curve theorem or a complete
algorithmic spanning-tree partition for arbitrary CMaps, both noted as
open work below.

## Euler-related results

| Result | Description |
|---|---|
| `euler_formula` | V + F = E + 2 for any `PlanarGraph` (Wiedijk #13) |
| `euler_int` | Signed form V - E + F = 2 |
| `platonic_classification` | The five Platonic solids (Wiedijk #50) |
| `petersenGraph_egirth_ge_5` | Petersen graph has girth ≥ 5 (formally proved) |
| `heawoodGraph_egirth_ge_6` | Heawood graph has girth ≥ 6 (formally proved) |
| `kn_not_planar` | K_n is not planar for any n ≥ 5 (infinite family, pure arithmetic) |
| `petersen_not_planar`, `heawood_not_planar` | Non-planarity via girth bounds |
| `girth_planarity_bound` | Edge bound from girth; implies K₅ and K₃,₃ cases |
| `petersenGraph_chromaticNumber_eq_3` | Petersen graph needs exactly 3 colors (Mathlib chromaticNumber API) |
| `edge_count_eq` | \|E\| = \|D\|/2 for any fixed-point-free involution |
| `eulerChar_of_spherical` | `IsSpherical → IsPlanar` via the CMap bridge |
| `isSpherical_iff_isPlanar` | Equivalence between the two internal planarity notions |
| `euler_via_vanStaudt` | Jordan-free Euler for any CMap satisfying the partition |
| `torusCMap_fails_vanStaudt` | Torus as explicit non-planar counterexample |

## Additional Wiedijk formalizations

These results live in this repository for convenience but are independent
of Euler's formula. Each is self-contained and could be extracted into its
own project.

| Result | Description |
|---|---|
| `cube_doubling_impossible` | ∛2 not in any 2-power-degree extension of ℚ (Wiedijk #8) |
| `desargues_theorem` | Desargues's theorem in ℙ K K³ over any commutative ring (Wiedijk #87) |

## Details

The combinatorial side is complete: inductive `PlanarGraph`, nine parametric
families, Platonic solid classification, non-planarity of K₅ and K₃,₃
(formally via `SimpleGraph`), concrete CMap witnesses for triangle through
octahedron, and a Jordan-free arithmetic derivation for explicit maps.

Petersen and Heawood are formally defined as `SimpleGraph (Fin n)` instances
with machine-verified edge counts. Their girth bounds are formally proved:
`petersenGraph_egirth_ge_5` and `heawoodGraph_egirth_ge_6` show all cycles
have length ≥ 5 and ≥ 6 respectively, using `Walk.IsCycle.getVert_injOn'` and
`adj_getVert_succ` from Mathlib, with `native_decide` for the finite cycle-free checks.

`kn_not_planar` establishes the infinite family: K_n is not planar for every n ≥ 5,
proved by pure arithmetic from Euler's formula (no `native_decide`). The key step
is `(n−4)(n−3) > 0` for n ≥ 5 via `nlinarith`, which forces 2E > 6n−12 while
Euler bounds 2E ≤ 6n−12. This subsumes all previous K₅/K₃,₃ cases.

`petersenGraph_chromaticNumber_eq_3` formally computes the chromatic number of the
Petersen graph using Mathlib's `SimpleGraph.chromaticNumber` API. The graph needs
exactly 3 colors: 3-colorability by explicit witness (`native_decide`), and
non-2-colorability because the 5-cycle is an odd cycle (`native_decide`).

`cube_doubling_impossible` (Wiedijk #8) proves that no field F/ℚ with [F:ℚ] = 2^k contains an
element cubing to 2. The algebraic core: X³ − 2 is irreducible over ℚ (Eisenstein at p=2 over ℤ,
lifted by Gauss's lemma), so [ℚ(∛2):ℚ] = 3 divides [F:ℚ] = 2^k, forcing 3 ∣ 2, contradiction.

## Open work

- Constructing the spanning-tree partition algorithmically for arbitrary CMaps
  (currently verified by `native_decide` on concrete instances).
- Connecting to topological planarity in ℝ², which requires either the
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
