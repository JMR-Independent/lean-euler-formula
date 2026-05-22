# Euler's polyhedron formula in Lean 4

Formalization of **V - E + F = 2** for planar graphs, built with
Lean 4 + Mathlib. Provides fully verified concrete witnesses alongside
the combinatorial-map approach proposed in mathlib4 PR #16074.

Over 100 theorems and definitions across 6 files, **0 sorry**,
CI green on every commit.

## Quick reference

| Result | File | Description |
|---|---|---|
| `euler_formula` | EulerMathlib | V + F = E + 2 for any PlanarGraph |
| `platonic_classification` | EulerMathlib | The 5 Platonic Solids Theorem (Wiedijk #38) |
| `petersen_not_planar` | EulerMathlib | The Petersen graph is not planar |
| `heawood_not_planar` | EulerMathlib | The Heawood graph is not planar |
| `girth_planarity_bound` | EulerMathlib | General girth-based edge bound for planar graphs |
| `planar_six_degree_bound` | EulerMathlib | 2E < 6V (key step toward 6-color theorem) |
| `vanStaudt_arith` | EulerMathlib | Arithmetic core of a Jordan-free route |
| `edge_count_eq` | Completeness | \|Edge\| = \|D\|/2 for any fixed-point-free involution |
| `eulerChar_of_spherical` | CMapEuler | IsSpherical → IsPlanar |
| `isSpherical_iff_isPlanar` | IsPlanarIffIsSpherical | Equivalence between the two internal notions of planarity used in this project |
| `euler_via_vanStaudt` | Hypermap | Jordan-free Euler theorem for any CMap with valid partition |
| `torusCMap_fails_vanStaudt` | Hypermap | The torus CMap fails the Van Staudt partition |

## Files

### `EulerMathlib.lean`

Inductive `PlanarGraph V E F` type with three constructors
(`point`, `addLeaf`, `addEdge`). `euler_formula` follows by structural
induction.

**Nine parametric families** (one theorem covers infinitely many graphs):
`path_planar`, `star_planar`, `cycle_planar`, `wheel_planar`,
`k2n_planar`, `prism_planar`, `antiprism_planar`,
`doubleWheel_planar`, `ladder_planar`.

**Hardcoded examples**: triangle, K₄, cube, octahedron, square,
dodecahedron, icosahedron (all five Platonic solids).

**Structural theorems**: vertex/face positivity, subdivision invariance,
gluing, tree characterization, edge bounds.

**Non-planarity**: `k5_not_planar`, `k33_not_planar`,
`K5_not_planarly_embeddable`, `petersen_not_planar`, `heawood_not_planar`.

**Platonic Solids Classification (Wiedijk #38)**: `platonic_constraint`,
`platonic_pairs_classification`, `platonic_classification`. Proves the
only regular planar polyhedra are tetrahedron, cube, octahedron,
dodecahedron, icosahedron.

**Girth bounds**: `girth_planarity_bound` (general),
`planar_six_degree_bound` (toward 6-color theorem).

**Jordan-free arithmetic core**: `vanStaudt_arith` proves V+F=E+2 from
the spanning-tree partition hypothesis (V-1)+(F-1) = E.

### `CMapEuler.lean`

Replicates the `CombinatorialMap` structure from mathlib4 PR #16074
verbatim. Defines `IsSpherical` as the bridge to `PlanarGraph` and
proves five concrete maps satisfy `IsPlanar` via `native_decide`:
- `singleEdgeMap` (2 darts, V=2, E=1, F=1)
- `triangleMap` (6 darts, V=3, E=3, F=2)
- `k4Map` (12 darts, V=4, E=6, F=4)
- `cubeMap` (24 darts, V=8, E=12, F=6)
- `octahedronMap` (24 darts, V=6, E=12, F=8)

Includes `planar_edge_bound`, `bipartite_planar_edge_bound`,
duality observations (`cube_octahedron_dual`, `k4_self_dual`),
and concrete-to-parametric bridges.

### `Completeness.lean`

Proves `edge_count_eq`: for any CombinatorialMap with a fixed-point-free
involution, the number of edges equals \|D\|/2 (fiber decomposition
using SameCycle and edgePerm² = 1).

Includes `torusCMap`: a valid connected CMap on 4 darts with
eulerCharacteristic = 0. A formally verified mathematical consequence
showing connectivity alone does not imply planarity.

### `IsPlanarIffIsSpherical.lean`

Proves `isSpherical_iff_isPlanar` for any connected CombinatorialMap.
The hard direction uses `PlanarGraph.ofEuler` to construct a witness
from the Euler equation alone, without topology or Jordan curve theorem.

Includes parametric-witness bridges:
`cubeMap_isPlanar_via_prism`,
`octahedronMap_isPlanar_via_antiprism`,
`triangleMap_isPlanar_via_cycle`.

### `GeometricEmbedding.lean`

Explicit ℝ² coordinates for `singleEdgeMap`, `triangleMap`, and
`k4Map`. Distinct-vertex theorems verified by `norm_num`.

### `Hypermap.lean` (Jordan-free approach in progress)

Infrastructure for the Dufourd/Gonthier-style hypermap reduction:
- `skipPerm`, `collapseEdge`, `collapseEdgePerm`: permutation surgery
- `walkupAt`, `MapsFixedPair`, `walkupAt_composition`: composition
  preservation
- `DufourdWalkupParameter`: framework for the inductive step

**Concrete Jordan-free Euler results** (Block 12-14):
- `singleEdgeMap_vanStaudt`, `triangleMap_vanStaudt`, `k4Map_vanStaudt`,
  `cubeMap_vanStaudt`, `octahedronMap_vanStaudt`: each concrete planar
  CMap satisfies the Van Staudt partition
- `*_euler_jordan_free`: V+F=E+2 derived purely arithmetically for each
- `torusCMap_fails_vanStaudt`: torus explicitly fails the partition
- `euler_via_vanStaudt`, `eulerChar_via_vanStaudt`: general reusable
  theorems for any CMap satisfying the partition hypothesis

## Scope

This project formalizes the combinatorial side of Euler's formula:
internal notions of planarity, concrete examples, structural theorems,
parametric families, and a Jordan-free derivation for explicit CMaps.

For arbitrary connected planar CMaps, constructing the spanning-tree
partition algorithmically (rather than verifying it by `native_decide`
on concrete instances) remains the substantive work ahead — this is
what would close the gap completely.

The connection to topological planarity (embeddability in ℝ² without
crossings) ultimately requires either the Jordan curve theorem
(not currently formalized in Lean 4 / Mathlib) or the Walkup-reduction
machinery (under development in `Hypermap.lean`).

## Related work

| System | Approach |
|---|---|
| HOL Light (Harrison, 2005) | Full topological JCT proof |
| Coq / Rocq (Gonthier 2005, Dufourd 2008) | Hypermap combinatorial Jordan |
| Isabelle (Bauer & Nipkow 2002) | Triangulations |
| Mathlib4 PR #16074 | Combinatorial map structure (open) |
| Mathlib4 PR #29639 | Homological algebra approach (closed) |
| **This repo** | Inductive PlanarGraph + concrete CMap witnesses + Jordan-free arithmetic core |

## Build

    lake build

CI runs on Lean 4.29.1 with Mathlib. All commits verified green by
GitHub Actions.
