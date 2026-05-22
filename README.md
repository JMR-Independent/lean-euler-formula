# Euler's polyhedron formula in Lean 4

Formalization of V - E + F = 2 for planar graphs, built using
Mathlib. Started as an attempt to provide concrete examples for
the `CombinatorialMap` structure from mathlib4 PR #16074.

## What's here

`EulerMathlib.lean`
Inductive `PlanarGraph V E F` type with three constructors
(`point`, `addLeaf`, `addEdge`). `euler_formula` follows by structural
induction. Includes:
  - hardcoded examples: triangle, K₄, cube, octahedron
  - parametric families: `path_planar`, `cycle_planar`, `wheel_planar`, `k2n_planar`
  - corollaries: `tree_edge_count`, `edge_bound`, `subdivide_preserves_euler`
  - non-planarity: `k5_not_planar`, `k33_not_planar`, `K5_not_planarly_embeddable`

`CMapEuler.lean`
Replicates the `CombinatorialMap` structure from PR #16074. Defines
`IsSpherical` as the bridge to `PlanarGraph` and proves five concrete
maps satisfy `IsPlanar` via `native_decide`:
  - `singleEdgeMap` (2 darts, V=2, E=1, F=1)
  - `triangleMap` (6 darts, V=3, E=3, F=2)
  - `k4Map` (12 darts, V=4, E=6, F=4)
  - `cubeMap` (24 darts, V=8, E=12, F=6)
  - `octahedronMap` (24 darts, V=6, E=12, F=8)

Also includes `planar_edge_bound` and `bipartite_planar_edge_bound`
applied to these examples (K₄ and octahedron saturate the 3V-6 bound).

`Completeness.lean`
Proves `edge_count_eq` (`Fintype.card M.Edge = Fintype.card D / 2`
for any CMap with a fixed-point-free involution). Includes `torusCMap`
as a counterexample: it is connected but has eulerChar = 0, showing
that connectivity alone does not imply planarity.

`IsPlanarIffIsSpherical.lean`
The algebraic equivalence `IsPlanar ↔ IsSpherical` for connected CMaps,
plus `all_examples_isSpherical_iff_isPlanar` verifying the full chain
for every concrete CMap.

`GeometricEmbedding.lean`
Explicit ℝ² coordinates for `singleEdgeMap`, `triangleMap`, and `k4Map`
demonstrating concrete planar realizations.

## What's not here

The topological direction, connecting `IsPlanar` to planar
embeddability in ℝ² via the Jordan curve theorem, is not closed.
This is an open problem across all proof assistants and would
require substantial topological infrastructure.

A separate experimental repository
(https://github.com/JMR-Independent/lean-euler-jordan-free) explores
Van Staudt's interdigitating spanning tree argument as a possible
Jordan-free route.

## Build

    lake build

CI runs on Lean 4.29.1 with Mathlib.
