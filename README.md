# Euler's polyhedron formula in Lean 4

Formalization of V - E + F = 2 for planar graphs, built using
Mathlib. Started as an attempt to provide concrete examples for
the `CombinatorialMap` structure from mathlib4 PR #16074.

## What's here

`EulerMathlib.lean`
inductive `PlanarGraph V E F` type with three constructors
(`point`, `addLeaf`, `addEdge`). `euler_formula` follows by structural
induction. Also includes `K5_not_planarly_embeddable` via Mathlib's
`SimpleGraph`.

`CMapEuler.lean`
replicates the `CombinatorialMap` structure from PR #16074. Defines
`IsSpherical` as the bridge to `PlanarGraph` and proves three concrete
maps satisfy `IsPlanar` via `native_decide`:
  - `singleEdgeMap` (2 darts, V=2, E=1, F=1)
  - `triangleMap` (6 darts, V=3, E=3, F=2)
  - `k4Map` (12 darts, V=4, E=6, F=4)

`Completeness.lean`
proves `edge_count_eq` (`Fintype.card M.Edge = Fintype.card D / 2`
for any CMap with a fixed-point-free involution). Includes `torusCMap`
as a counterexample showing that connected CMaps need not be planar.

`IsPlanarIffIsSpherical.lean`
the algebraic equivalence `IsPlanar ↔ IsSpherical` for connected CMaps.

`GeometricEmbedding.lean`
explicit ℝ² coordinates for `singleEdgeMap`, `triangleMap`, and `k4Map`
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
