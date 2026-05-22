# Euler's polyhedron formula in Lean 4

Formalization of V - E + F = 2 for planar graphs, built using
Mathlib. Started as an attempt to provide concrete examples for
the `CombinatorialMap` structure from mathlib4 PR #16074.

## What's here

### `EulerMathlib.lean`

Inductive `PlanarGraph V E F` type with three constructors
(`point`, `addLeaf`, `addEdge`). `euler_formula` follows by structural
induction.

**Parametric families** (one theorem covers infinitely many graphs):
- `path_planar n`: path on n vertices (V=n, E=n-1, F=1)
- `star_planar n`: star K_{1,n} (V=n+1, E=n, F=1)
- `cycle_planar n`: cycle C_n (V=n, E=n, F=2)
- `wheel_planar n`: wheel W_n (V=n+1, E=2n, F=n+1)
- `k2n_planar n`: complete bipartite K_{2,n} (V=n+2, E=2n, F=n)
- `prism_planar n`: n-gonal prism (V=2n, E=3n, F=n+2)
- `antiprism_planar n`: n-gonal antiprism (V=2n, E=4n, F=2n+2)

**Hardcoded examples**: triangle, K₄, cube, octahedron.

**Structural theorems**:
- `vertex_pos`, `face_pos`: V, F ≥ 1
- `tree_edge_count`: trees satisfy E = V - 1
- `one_face_iff_tree`, `no_edges_iff_point`
- `subdivide_preserves_euler`, `subdivide_k_times`
- `euler_swap_VF`: symmetric form
- `glue_preserves_euler`: vertex-gluing preserves Euler
- `max_edges_planar`, `min_edges_planar`
- `edge_bound`, `bipartite_edge_bound`

**Non-planarity**: `k5_not_planar`, `k33_not_planar`, `K5_not_planarly_embeddable`.

### `CMapEuler.lean`

Replicates the `CombinatorialMap` structure from PR #16074. Defines
`IsSpherical` as the bridge to `PlanarGraph` and proves five concrete
maps satisfy `IsPlanar` via `native_decide`:
- `singleEdgeMap` (2 darts, V=2, E=1, F=1)
- `triangleMap` (6 darts, V=3, E=3, F=2)
- `k4Map` (12 darts, V=4, E=6, F=4)
- `cubeMap` (24 darts, V=8, E=12, F=6)
- `octahedronMap` (24 darts, V=6, E=12, F=8)

Includes `planar_edge_bound`, `bipartite_planar_edge_bound`,
`cube_octahedron_dual`, `k4_self_dual`.

### `Completeness.lean`

Proves `edge_count_eq` (`Fintype.card M.Edge = Fintype.card D / 2`
for any CMap with a fixed-point-free involution). Includes `torusCMap`
as a counterexample: it is connected but has eulerChar = 0, showing
that connectivity alone does not imply planarity.

### `IsPlanarIffIsSpherical.lean`

The algebraic equivalence `IsPlanar ↔ IsSpherical` for connected CMaps,
plus `all_examples_isSpherical_iff_isPlanar` verifying the full chain
for every concrete CMap.

### `GeometricEmbedding.lean`

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
