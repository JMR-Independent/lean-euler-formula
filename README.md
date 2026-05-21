# Euler's polyhedron formula in Lean 4

Formalization of V - E + F = 2 for planar graphs, built using
Mathlib. Started as an attempt to provide concrete examples for
the `CombinatorialMap` structure from mathlib4 PR #16074.

## What's here

- `EulerMathlib.lean`: inductive `PlanarGraph V E F` type with three
  constructors (`point`, `addLeaf`, `addEdge`). `euler_formula` follows
  by structural induction.
- `CMapEuler.lean`: replicates the `CombinatorialMap` structure from
  PR #16074, defines `IsSpherical` as the bridge to `PlanarGraph`,
  proves `triangleMap.IsPlanar` and `k4Map.IsPlanar` via `native_decide`.
- `Completeness.lean`: proves `edge_count_eq`
  (`Fintype.card M.Edge = Fintype.card D / 2` for any CMap with a
  fixed-point-free involution). Includes `torusCMap` as a counterexample
  showing that connected CMaps need not be planar.
- `IsPlanarIffIsSpherical.lean`: the algebraic equivalence
  `IsPlanar ↔ IsSpherical` for connected CMaps.

## What's not here

The topological direction, connecting `IsPlanar` to planar
embeddability in ℝ² via the Jordan curve theorem, is not closed.
This is an open problem across all proof assistants and would
require substantial topological infrastructure.

## Build

    lake build

CI runs on Lean 4.29.1 with Mathlib.
