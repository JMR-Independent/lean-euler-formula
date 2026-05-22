# Euler's polyhedron formula in Lean 4

Formalization of **V - E + F = 2** for planar graphs, built with
Lean 4 + Mathlib. 100 theorems and definitions, 1675 lines of code,
**0 sorry**, CI green on every commit.

Originated as concrete examples for the `CombinatorialMap` structure
proposed in mathlib4 PR #16074, which has been open without concrete
witnesses since August 2024.

## Quick reference

| Result | File | Description |
|---|---|---|
| `euler_formula` | EulerMathlib | V + F = E + 2 for any PlanarGraph |
| `euler_int` | EulerMathlib | Signed form: V - E + F = 2 |
| `edge_count_eq` | Completeness | |Edge| = |D|/2 for any fixed-point-free involution |
| `eulerChar_of_spherical` | CMapEuler | IsSpherical → IsPlanar |
| `isSpherical_iff_isPlanar` | IsPlanarIffIsSpherical | Full equivalence for connected CMaps |
| `torusCMap_not_isSpherical` | IsPlanarIffIsSpherical | Connected ≠ planar (counterexample) |

## File breakdown

### `EulerMathlib.lean` (611 lines)

Defines `PlanarGraph V E F` as an inductive proposition with three
constructors corresponding to elementary planar operations:

- `point`: a single vertex (V=1, E=0, F=1)
- `addLeaf`: attach a pendant vertex (V+1, E+1, F)
- `addEdge`: split a face by adding an edge (V, E+1, F+1)

The main theorem `euler_formula` proves V + F = E + 2 by structural
induction; each case closes by `omega`.

**Nine parametric families** (one theorem per family covers infinitely
many graphs):
- `path_planar n`: path on n vertices
- `star_planar n`: star K_{1,n}
- `cycle_planar n`: cycle C_n
- `wheel_planar n`: wheel W_n
- `k2n_planar n`: complete bipartite K_{2,n}
- `prism_planar n`: n-gonal prism
- `antiprism_planar n`: n-gonal antiprism
- `doubleWheel_planar n`: double wheel DW_n
- `ladder_planar n`: ladder L_n

**Hardcoded examples**: triangle, K₄, cube, octahedron, square.

**Structural theorems**:
- `vertex_pos`, `face_pos`: V, F ≥ 1
- `edge_le_vertex_plus_face`: E ≤ V + F - 2
- `no_edges_iff_point`, `one_face_iff_tree`
- `subdivide_preserves_euler`, `subdivide_k_times`
- `euler_swap_VF`, `glue_preserves_euler`
- `max_edges_planar`, `min_edges_planar`
- `tree_edge_count`, `triangulation_edges`

**Non-planarity**: `k5_not_planar`, `k33_not_planar`,
`K5_not_planarly_embeddable` (via Mathlib's SimpleGraph).

### `CMapEuler.lean` (528 lines)

Replicates the `CombinatorialMap` structure from mathlib4 PR #16074
verbatim. A combinatorial map is a finite set of darts with three
permutations satisfying `face * edge * vertex = 1`, where `edge` is
a fixed-point-free involution.

Defines `IsSpherical M ↔ ∃ V E F, PlanarGraph V E F ∧ |M.Vertex| = V
∧ |M.Edge| = E ∧ |M.Face| = F`. The bridge theorem
`eulerChar_of_spherical` proves IsSpherical → IsPlanar
(eulerCharacteristic = 2) by applying our PlanarGraph euler_int.

**Five concrete CMaps proved IsPlanar via `native_decide`**:
- `singleEdgeMap`: 2 darts, 1 edge between 2 vertices (V=2, E=1, F=1)
- `triangleMap`: 6 darts, triangle K₃ (V=3, E=3, F=2)
- `k4Map`: 12 darts, complete graph K₄ (V=4, E=6, F=4)
- `cubeMap`: 24 darts, cube (V=8, E=12, F=6)
- `octahedronMap`: 24 darts, octahedron (V=6, E=12, F=8)

**Edge bounds for CMaps**:
- `planar_edge_bound`: E ≤ 3V - 6 with face-degree hypothesis
- `bipartite_planar_edge_bound`: E ≤ 2V - 4 for bipartite faces

**Polyhedral observations**:
- `cube_octahedron_dual`: V_cube=F_octa, E_cube=E_octa, F_cube=V_octa
- `k4_self_dual`: K₄ has V = F
- `octahedron_matches_antiprism`, `cube_matches_square_prism`,
  `triangle_matches_cycle`: concrete = parametric

### `Completeness.lean` (240 lines)

Proves `edge_count_eq`: for any CombinatorialMap with a fixed-point-free
involution `edge`, the number of edges equals |D|/2. The proof uses:

- `edgePerm_no_fixedPoint`, `edgePerm_support_eq_univ`
- `edgePerm_sq`: edge² = 1
- `edgePerm_cycleType_mem`: all cycle lengths equal 2
- `edgePerm_sameCycle_iff`: SameCycle iff in same 2-element orbit
- `edgePerm_fiber_card`: each orbit has exactly 2 elements
- Final: fiber decomposition |D| = Σ_e 2 = 2|Edge|

Includes `torusCMap`: a valid connected CMap on 4 darts (V=1, E=2, F=1,
eulerChar = 0). This is a counterexample showing that connectivity
alone does not imply planarity — the genus matters.

### `IsPlanarIffIsSpherical.lean` (174 lines)

Proves `isSpherical_iff_isPlanar` for any connected CombinatorialMap.

The hard direction (IsPlanar → IsSpherical) uses `PlanarGraph.ofEuler`:
from V ≥ 1 and V + F = E + 2, construct a PlanarGraph witness by
induction on E:
- E = 0: must be `point` (V=1, F=1)
- E > 0, V > 1: use `addLeaf`
- E > 0, V = 1: use `addEdge`

**No Jordan curve theorem, no spanning trees, no topology required.**
The equivalence is purely algebraic.

Concrete consequences:
- `torusCMap_not_isSpherical`: the torus CMap fails the equivalence
  (consistent with the genus-0 hypothesis being essential)
- `all_examples_isSpherical_iff_isPlanar`: chain verified for all 5
  concrete CMaps end-to-end
- `cubeMap_isPlanar_via_prism`, `octahedronMap_isPlanar_via_antiprism`,
  `triangleMap_isPlanar_via_cycle`: each concrete CMap proved IsPlanar
  using a parametric PlanarGraph witness (alternative to the hardcoded one)

### `GeometricEmbedding.lean` (122 lines)

Explicit ℝ² coordinates for the concrete CMaps:
- `singleEdgeLayout`: endpoints (0,0) and (1,0)
- `triangleLayout`: corners (0,0), (1,0), (1/2, 1)
- `k4Layout`: triangle ABC with D inside

Each layout satisfies `same_vertex_same_pos`: darts in the same vertex
orbit get the same coordinates. Theorems like
`triangle_layout_distinct_vertices` verify different vertices map to
different points.

## What's NOT here

The topological direction — proving that every graph embeddable in ℝ²
without crossings satisfies our `IsPlanar` — is **not** closed. This
would require the Jordan curve theorem, which has not been formalized
in Lean 4 / Mathlib (only in HOL Light by Harrison, 59,000 lines).

A separate experimental repository
(https://github.com/JMR-Independent/lean-euler-jordan-free) explores
Van Staudt's interdigitating spanning tree argument as a possible
Jordan-free route. The arithmetic core (`vanStaudt_arith`) compiles,
but the substantive combinatorial work of constructing spanning trees
is not yet implemented.

## Comparison with prior work

| System | Pick / Euler status |
|---|---|
| HOL Light (Harrison, 2005) | Full topological JCT proof, 59,000 lines |
| Coq / Rocq (Gonthier 2005, Dufourd 2008) | Hypermap combinatorial Jordan |
| Isabelle (Bauer & Nipkow 2002) | Restricted to triangulations only |
| Mathlib4 PR #16074 | Structure defined, no concrete examples (9 months stalled) |
| Mathlib4 PR #29639 (jessealama) | Homological algebra approach, abandoned |
| **This repo** | **5 concrete CMaps proved IsPlanar, 9 parametric families, 0 sorry** |

## Build

    lake build

CI runs on Lean 4.29.1 with Mathlib. All commits verified green by
GitHub Actions.
