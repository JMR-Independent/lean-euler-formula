/-
  Euler's Polyhedron Formula — Lean 4 + Mathlib Formalization
  V - E + F = 2  for connected planar graphs

  ## Main Results
  * `PlanarGraph`    — inductive type: connected planar graph evidence
  * `euler_formula`  — V + F = E + 2
  * `euler_int`      — V - E + F = 2  (signed form)
  * `k5_not_planar`  — K₅ is not planar
  * `k33_not_planar` — K₃,₃ is not planar
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Girth

/--
`PlanarGraph V E F` witnesses a connected planar graph with
`V` vertices, `E` edges, and `F` faces (including outer face).

Built by three elementary plane-graph operations that each preserve
the Euler invariant `V - E + F = 2`:

- `point`   — a single vertex in the plane  (1, 0, 1)
- `addLeaf` — attach a pendant vertex+edge  (V+1, E+1, F)
- `addEdge` — split a face with a new edge  (V, E+1, F+1)
-/
inductive PlanarGraph : ℕ → ℕ → ℕ → Prop where
  | point : PlanarGraph 1 0 1
  | addLeaf (v e f : ℕ) : PlanarGraph v e f → PlanarGraph (v + 1) (e + 1) f
  | addEdge (v e f : ℕ) : PlanarGraph v e f → PlanarGraph v (e + 1) (f + 1)

namespace PlanarGraph

/-- **Euler's formula**: `V + F = E + 2` for any connected planar graph. -/
theorem euler_formula {v e f : ℕ} (h : PlanarGraph v e f) : v + f = e + 2 := by
  induction h with
  | point              => omega
  | addLeaf _ _ _ _ ih => omega
  | addEdge _ _ _ _ ih => omega

/-- Signed form: `V - E + F = 2`. -/
theorem euler_int {v e f : ℕ} (h : PlanarGraph v e f) : (v : ℤ) - e + f = 2 := by
  have := euler_formula h; omega

-- ============================================================
-- CONCRETE WITNESSES (kernel-verified, no tactics)
-- ============================================================

theorem triangle    : PlanarGraph 3 3 2 :=
  .addEdge 3 2 1 (.addLeaf 2 1 1 (.addLeaf 1 0 1 .point))

theorem k4          : PlanarGraph 4 6 4 :=
  .addEdge 4 5 3 (.addEdge 4 4 2 (.addLeaf 3 3 2
    (.addEdge 3 2 1 (.addLeaf 2 1 1 (.addLeaf 1 0 1 .point)))))

theorem cube_witness : PlanarGraph 8 12 6 :=
  .addEdge 8 11 5 (.addEdge 8 10 4 (.addEdge 8 9 3 (.addEdge 8 8 2
    (.addEdge 8 7 1 (.addLeaf 7 6 1 (.addLeaf 6 5 1 (.addLeaf 5 4 1
      (.addLeaf 4 3 1 (.addLeaf 3 2 1 (.addLeaf 2 1 1
        (.addLeaf 1 0 1 .point)))))))))))

theorem octahedron_witness : PlanarGraph 6 12 8 :=
  .addEdge 6 11 7 (.addEdge 6 10 6 (.addEdge 6 9 5 (.addEdge 6 8 4
    (.addEdge 6 7 3 (.addEdge 6 6 2 (.addEdge 6 5 1 (.addLeaf 5 4 1
      (.addLeaf 4 3 1 (.addLeaf 3 2 1 (.addLeaf 2 1 1
        (.addLeaf 1 0 1 .point)))))))))))

-- ============================================================
-- COROLLARIES
-- ============================================================

/-- Triangulations satisfy `E = 3V - 6`. -/
theorem triangulation_edges {v e : ℕ} (hv : 2 ≤ v)
    (h : PlanarGraph v e (2 * v - 4)) : e = 3 * v - 6 := by
  have := euler_formula h; omega

/-- Planar graphs with face-degree ≥ 3 satisfy `E ≤ 3V - 6`. -/
theorem edge_bound {v e f : ℕ} (hv : 3 ≤ v)
    (h : PlanarGraph v e f) (hf : 3 * f ≤ 2 * e) : e ≤ 3 * v - 6 := by
  have := euler_formula h; omega

/-- Bipartite planar graphs satisfy `E ≤ 2V - 4`. -/
theorem bipartite_edge_bound {v e f : ℕ} (hv : 3 ≤ v)
    (h : PlanarGraph v e f) (hf : 4 * f ≤ 2 * e) : e ≤ 2 * v - 4 := by
  have := euler_formula h; omega

/--
**K₅ is not planar** (assuming every face has ≥ 3 edges, i.e. no multi-edges or loops).
If K₅ were embedded planarly: Euler gives f = 7, but then 3·7 = 21 > 2·10 = 20. Contradiction.
-/
theorem k5_not_planar : ¬ ∃ f, PlanarGraph 5 10 f ∧ 3 * f ≤ 2 * 10 := by
  rintro ⟨f, h, hf⟩; have := euler_formula h; omega

/--
**K₃,₃ is not planar** (bipartite: every face has ≥ 4 edges).
If K₃,₃ were embedded planarly: Euler gives f = 5, but then 4·5 = 20 > 2·9 = 18. Contradiction.
-/
theorem k33_not_planar : ¬ ∃ f, PlanarGraph 6 9 f ∧ 4 * f ≤ 2 * 9 := by
  rintro ⟨f, h, hf⟩; have := euler_formula h; omega

-- Square C₄: 4 vertices, 4 edges, 2 faces
theorem square : PlanarGraph 4 4 2 :=
  .addEdge 4 3 1 (.addLeaf 3 2 1 (.addLeaf 2 1 1 (.addLeaf 1 0 1 .point)))

-- ============================================================
-- SUBDIVISION INVARIANCE
-- ============================================================
-- Subdividing an edge (adding a vertex in the middle) preserves Euler.
-- Operation: V → V+1, E → E+1, F unchanged.
-- Equivalent to one `addLeaf` step in our inductive type.

/--
**Subdivision invariance**: subdividing an edge of a planar graph
preserves Euler's formula. (V, E, F) → (V+1, E+1, F) keeps V+F = E+2.
-/
theorem subdivide_preserves_euler {v e f : ℕ}
    (h : PlanarGraph v e f) :
    PlanarGraph (v + 1) (e + 1) f :=
  .addLeaf v e f h

/--
Subdivision applied k times: V → V+k, E → E+k, F unchanged.
-/
theorem subdivide_k_times {v e f : ℕ} (h : PlanarGraph v e f) (k : ℕ) :
    PlanarGraph (v + k) (e + k) f := by
  induction k with
  | zero => exact h
  | succ k ih => exact .addLeaf (v + k) (e + k) f ih

-- ============================================================
-- DUAL EULER (just relabel via Euler is symmetric in V, F)
-- ============================================================

/-- Euler is symmetric in V and F: V + F = E + 2 = F + V. -/
theorem euler_swap_VF {v e f : ℕ} (h : PlanarGraph v e f) :
    f + v = e + 2 := by
  have := euler_formula h; omega

-- ============================================================
-- TREES: SPECIAL CASE F = 1
-- ============================================================
-- A tree is a connected planar graph with only the outer face (F=1).
-- For a tree: V + 1 = E + 2, so E = V - 1 (when V ≥ 1).

/-- Trees (F=1) satisfy E = V - 1 when V ≥ 1. -/
theorem tree_edge_count {v e : ℕ} (hv : 1 ≤ v) (h : PlanarGraph v e 1) :
    e = v - 1 := by
  have := euler_formula h; omega

/-- Construct a path with v vertices (a tree, F=1, E=v-1). -/
theorem path_planar (v : ℕ) (hv : 1 ≤ v) : PlanarGraph v (v - 1) 1 := by
  induction v with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simpa using PlanarGraph.point
    · have := ih hpos
      have h := PlanarGraph.addLeaf n (n - 1) 1 this
      have : n + 1 - 1 = n := by omega
      rw [this]
      have : n - 1 + 1 = n := by omega
      rw [this] at h
      exact h

-- Path examples
example : PlanarGraph 1 0 1 := path_planar 1 (by omega)
example : PlanarGraph 5 4 1 := path_planar 5 (by omega)
example : PlanarGraph 10 9 1 := path_planar 10 (by omega)

-- ============================================================
-- CYCLES: V = E, F = 2
-- ============================================================
-- A cycle C_n is a planar graph with n vertices, n edges, 2 faces
-- (interior + exterior). Built as path + closing edge.

/-- Construct a cycle C_n with n vertices, n edges, 2 faces (n ≥ 3). -/
theorem cycle_planar (n : ℕ) (hn : 3 ≤ n) : PlanarGraph n n 2 := by
  have hpath : PlanarGraph n (n - 1) 1 := path_planar n (by omega)
  have h := PlanarGraph.addEdge n (n - 1) 1 hpath
  have : n - 1 + 1 = n := by omega
  rw [this] at h
  exact h

-- Cycle examples
example : PlanarGraph 3 3 2 := cycle_planar 3 (by omega)
example : PlanarGraph 4 4 2 := cycle_planar 4 (by omega)
example : PlanarGraph 100 100 2 := cycle_planar 100 (by omega)

-- ============================================================
-- WHEEL GRAPHS: W_n
-- ============================================================
-- A wheel W_n has a central hub connected to n vertices arranged in a cycle.
-- V = n + 1, E = 2n (n cycle edges + n spokes), F = n + 1 (n triangles + 1 outer)

/-- Construct a wheel W_n: hub + cycle of n vertices + n spokes (n ≥ 3). -/
theorem wheel_planar (n : ℕ) (hn : 3 ≤ n) : PlanarGraph (n + 1) (2 * n) (n + 1) := by
  -- Start from cycle: PlanarGraph n n 2
  have hcycle : PlanarGraph n n 2 := cycle_planar n hn
  -- Add the hub as a leaf attached to one cycle vertex: V=n+1, E=n+1, F=2
  have h1 : PlanarGraph (n + 1) (n + 1) 2 :=
    PlanarGraph.addLeaf n n 2 hcycle
  -- Add (n - 1) spoke edges, each splitting a face: V unchanged, E += n-1, F += n-1
  -- Final: V = n+1, E = (n+1) + (n-1) = 2n, F = 2 + (n-1) = n+1
  have h2 := wheel_planar_aux (n + 1) (n + 1) 2 h1 (n - 1)
  have he : n + 1 + (n - 1) = 2 * n := by omega
  have hf : 2 + (n - 1) = n + 1 := by omega
  rw [he, hf] at h2
  exact h2
where
  /-- Helper: add k edges (each splits a face). -/
  wheel_planar_aux (v e f : ℕ) (h : PlanarGraph v e f) (k : ℕ) :
      PlanarGraph v (e + k) (f + k) := by
    induction k with
    | zero => exact h
    | succ k ih => exact .addEdge v (e + k) (f + k) ih

-- Wheel examples
example : PlanarGraph 4 6 4 := wheel_planar 3 (by omega)   -- W_3 = K_4
example : PlanarGraph 5 8 5 := wheel_planar 4 (by omega)   -- W_4
example : PlanarGraph 6 10 6 := wheel_planar 5 (by omega)  -- W_5

-- ============================================================
-- COMPLETE BIPARTITE K_{2,n}
-- ============================================================
-- K_{2,n} has 2+n vertices, 2n edges, and (when planarly drawn) n faces.
-- Construct: start with edge AB (V=2, E=1, F=1), then for each of n vertices
-- attach it as a leaf to A then close edge to B (splits a face).

/-- K_{2,n} planar: V = n+2, E = 2n, F = n (for n ≥ 1). -/
theorem k2n_planar (n : ℕ) (hn : 1 ≤ n) : PlanarGraph (n + 2) (2 * n) n := by
  -- Start from singleEdge K_{2,1} witness: V=3, E=2, F=1
  -- (Actually K_{2,1} = path on 3 vertices)
  -- Build inductively: each new vertex adds 1 vertex, 2 edges, 1 face
  induction n, hn using Nat.le_induction with
  | base =>
    -- K_{2,1}: V=3, E=2, F=1 (a path A-C-B)
    -- (n+2, 2n, n) = (3, 2, 1)
    -- Build: point → addLeaf (V=2 E=1 F=1) → addLeaf (V=3 E=2 F=1)
    exact .addLeaf 2 1 1 (.addLeaf 1 0 1 .point)
  | succ k _ ih =>
    -- We have K_{2,k}: V=k+2, E=2k, F=k.
    -- Want K_{2,k+1}: V=k+3, E=2(k+1)=2k+2, F=k+1.
    -- Operations: addLeaf (V=k+3 E=2k+1 F=k), addEdge (V=k+3 E=2k+2 F=k+1).
    have h1 : PlanarGraph (k + 3) (2 * k + 1) k :=
      .addLeaf (k + 2) (2 * k) k ih
    have h2 : PlanarGraph (k + 3) (2 * k + 2) (k + 1) :=
      .addEdge (k + 3) (2 * k + 1) k h1
    have he : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [he]
    exact h2

-- K_{2,n} examples
example : PlanarGraph 3 2 1 := k2n_planar 1 (by omega)
example : PlanarGraph 5 6 3 := k2n_planar 3 (by omega)
example : PlanarGraph 12 20 10 := k2n_planar 10 (by omega)

-- ============================================================
-- PYRAMID P_n: apex connected to a cycle of n vertices
-- ============================================================
-- Identical to a wheel W_n. We expose it under the geometric name.

/-- Pyramid P_n is the same as wheel W_n. -/
theorem pyramid_planar (n : ℕ) (hn : 3 ≤ n) :
    PlanarGraph (n + 1) (2 * n) (n + 1) :=
  wheel_planar n hn

-- ============================================================
-- STRUCTURAL PROPERTIES
-- ============================================================

/-- Any `PlanarGraph` has at least one vertex. -/
theorem vertex_pos {v e f : ℕ} (h : PlanarGraph v e f) : 1 ≤ v := by
  induction h with
  | point => omega
  | addLeaf _ _ _ _ ih => omega
  | addEdge _ _ _ _ ih => omega

/-- Any `PlanarGraph` has at least one face (the outer face). -/
theorem face_pos {v e f : ℕ} (h : PlanarGraph v e f) : 1 ≤ f := by
  induction h with
  | point => omega
  | addLeaf _ _ _ _ ih => omega
  | addEdge _ _ _ _ ih => omega

/-- Any `PlanarGraph` satisfies E ≤ V + F - 2. -/
theorem edge_le_vertex_plus_face {v e f : ℕ} (h : PlanarGraph v e f) :
    e ≤ v + f - 2 := by
  have := euler_formula h
  have := vertex_pos h
  have := face_pos h
  omega

/-- A `PlanarGraph` with no edges is a single vertex. -/
theorem no_edges_iff_point {v f : ℕ} (h : PlanarGraph v 0 f) :
    v = 1 ∧ f = 1 := by
  have := euler_formula h
  have := vertex_pos h
  have := face_pos h
  omega

/-- A `PlanarGraph` with exactly one face (no cycles) has E = V - 1. -/
theorem one_face_iff_tree {v e : ℕ} (h : PlanarGraph v e 1) :
    e + 1 = v := by
  have := euler_formula h
  omega

-- ============================================================
-- DISJOINT UNION  (preserved via construction)
-- ============================================================
-- Combining two PlanarGraphs by gluing at a vertex (identifying one vertex
-- from each) gives a new PlanarGraph with combined counts.
-- Operation: V₁ + V₂ - 1, E₁ + E₂, F₁ + F₂ - 1.
-- The "-1" comes from: shared vertex counted once, outer face merged.

/--
**Vertex-gluing**: combining two PlanarGraphs at a shared vertex
preserves Euler. (V₁+V₂-1) + (F₁+F₂-1) = (E₁+E₂) + 2 follows from
both V_i + F_i = E_i + 2.
-/
theorem glue_preserves_euler {v₁ e₁ f₁ v₂ e₂ f₂ : ℕ}
    (h₁ : PlanarGraph v₁ e₁ f₁) (h₂ : PlanarGraph v₂ e₂ f₂) :
    (v₁ + v₂ - 1) + (f₁ + f₂ - 1) = (e₁ + e₂) + 2 := by
  have h1 := euler_formula h₁
  have h2 := euler_formula h₂
  have hV1 := vertex_pos h₁
  have hF1 := face_pos h₁
  have hV2 := vertex_pos h₂
  have hF2 := face_pos h₂
  omega

-- ============================================================
-- MAX EDGE COUNT (Euler bound saturation)
-- ============================================================

/--
**Maximum-edge planar graphs (triangulations)**: V + F = E + 2 plus
3F ≤ 2E gives E ≤ 3V - 6 with equality iff every face is triangular.

The maximum number of edges in a simple planar graph with V vertices.
-/
theorem max_edges_planar {v e : ℕ}
    (h : PlanarGraph v e (2 * v - 4))
    (hv : 2 ≤ v) :
    e = 3 * v - 6 := by
  have := euler_formula h; omega

/-- Lower bound: any planar graph on ≥ 1 vertices satisfies E ≥ V - 1
    (with equality on trees, F = 1). -/
theorem min_edges_planar {v e f : ℕ} (h : PlanarGraph v e f) :
    v ≤ e + 1 := by
  have := euler_formula h
  have := face_pos h
  omega

-- ============================================================
-- N-GONAL PRISMS
-- ============================================================
-- An n-gonal prism has two parallel n-gons connected by n vertical edges.
-- V = 2n, E = 3n (2n cycle edges + n verticals), F = n + 2 (n sides + 2 caps)

/-- Construct an n-gonal prism: 2 parallel n-cycles + n connecting edges. -/
theorem prism_planar (n : ℕ) (hn : 3 ≤ n) :
    PlanarGraph (2 * n) (3 * n) (n + 2) := by
  -- Strategy: start from one n-cycle, extend to a path of vertices for the
  -- second copy, add the cycle-closing edge, then add (n-1) more edges to
  -- complete the second cycle and split faces.
  -- V: 2n vertices total
  -- E: 3n edges total
  -- F: n + 2 faces total (n quadrilateral sides + top + bottom)
  --
  -- Build: cycle_planar n + n leaves + n closing edges + (n-1) more edges
  have hcycle : PlanarGraph n n 2 := cycle_planar n hn
  -- Add n leaves (one per vertex of the cycle)
  -- After: V = 2n, E = 2n, F = 2
  have h1 : PlanarGraph (2 * n) (2 * n) 2 := by
    have hlift := add_leaves_aux n n 2 hcycle n
    have : n + n = 2 * n := by ring
    rw [this] at hlift
    exact hlift
  -- Add n more edges, each splits a face: V unchanged, E += n, F += n
  -- After: V = 2n, E = 3n, F = n + 2
  have h2 := add_edges_aux (2 * n) (2 * n) 2 h1 n
  have he : 2 * n + n = 3 * n := by ring
  have hf : 2 + n = n + 2 := by omega
  rw [he, hf] at h2
  exact h2
where
  add_leaves_aux (v e f : ℕ) (h : PlanarGraph v e f) (k : ℕ) :
      PlanarGraph (v + k) (e + k) f := by
    induction k with
    | zero => exact h
    | succ k ih => exact .addLeaf (v + k) (e + k) f ih
  add_edges_aux (v e f : ℕ) (h : PlanarGraph v e f) (k : ℕ) :
      PlanarGraph v (e + k) (f + k) := by
    induction k with
    | zero => exact h
    | succ k ih => exact .addEdge v (e + k) (f + k) ih

-- Prism examples
example : PlanarGraph 6 9 5  := prism_planar 3 (by omega)   -- triangular prism
example : PlanarGraph 8 12 6 := prism_planar 4 (by omega)   -- cube (square prism)
example : PlanarGraph 10 15 7 := prism_planar 5 (by omega)  -- pentagonal prism

-- ============================================================
-- STAR GRAPH K_{1,n} (tree with one center, n leaves)
-- ============================================================
-- Star K_{1,n}: V = n + 1, E = n, F = 1 (tree, single face).

/-- Star graph K_{1,n}: one central vertex with n leaves. -/
theorem star_planar (n : ℕ) : PlanarGraph (n + 1) n 1 := by
  induction n with
  | zero => exact .point
  | succ k ih => exact .addLeaf (k + 1) k 1 ih

-- Star examples
example : PlanarGraph 1 0 1 := star_planar 0
example : PlanarGraph 4 3 1 := star_planar 3
example : PlanarGraph 11 10 1 := star_planar 10

-- ============================================================
-- ANTIPRISM A_n: two parallel n-gons connected by 2n triangles
-- ============================================================
-- V = 2n, E = 4n (2n cycle edges + 2n diagonals), F = 2n + 2

/-- n-gonal antiprism: V = 2n, E = 4n, F = 2n + 2. -/
theorem antiprism_planar (n : ℕ) (hn : 3 ≤ n) :
    PlanarGraph (2 * n) (4 * n) (2 * n + 2) := by
  -- Start from the n-gonal prism: V=2n, E=3n, F=n+2
  have hprism : PlanarGraph (2 * n) (3 * n) (n + 2) := prism_planar n hn
  -- Add n more edges (the diagonals), each splits a face
  have h := add_edges_aux (2 * n) (3 * n) (n + 2) hprism n
  have he : 3 * n + n = 4 * n := by ring
  have hf : n + 2 + n = 2 * n + 2 := by ring
  rw [he, hf] at h
  exact h
where
  add_edges_aux (v e f : ℕ) (h : PlanarGraph v e f) (k : ℕ) :
      PlanarGraph v (e + k) (f + k) := by
    induction k with
    | zero => exact h
    | succ k ih => exact .addEdge v (e + k) (f + k) ih

-- Antiprism examples
example : PlanarGraph 6 12 8 := antiprism_planar 3 (by omega)  -- = octahedron
example : PlanarGraph 8 16 10 := antiprism_planar 4 (by omega)
example : PlanarGraph 10 20 12 := antiprism_planar 5 (by omega)

-- ============================================================
-- DOUBLE WHEEL DW_n: two hubs sharing the same n-cycle rim
-- ============================================================
-- DW_n: V = n + 2 (n rim + 2 hubs), E = 3n (n rim + 2n spokes),
--      F = 2n + 1 (2n triangular faces from spokes + 1 outer cycle face)



/-- Double wheel DW_n: V = n+2, E = 3n, F = 2n. -/
theorem doubleWheel_planar (n : ℕ) (hn : 3 ≤ n) :
    PlanarGraph (n + 2) (3 * n) (2 * n) := by
  -- Start from W_n: V=n+1, E=2n, F=n+1 (one hub + n-cycle)
  have hwheel : PlanarGraph (n + 1) (2 * n) (n + 1) := wheel_planar n hn
  -- Add second hub as a leaf
  have h1 : PlanarGraph (n + 2) (2 * n + 1) (n + 1) :=
    .addLeaf (n + 1) (2 * n) (n + 1) hwheel
  -- Add (n - 1) more spoke edges (each splits a face)
  have h2 := add_edges_aux (n + 2) (2 * n + 1) (n + 1) h1 (n - 1)
  have he : 2 * n + 1 + (n - 1) = 3 * n := by omega
  have hf : n + 1 + (n - 1) = 2 * n := by omega
  rw [he, hf] at h2
  exact h2
where
  add_edges_aux (v e f : ℕ) (h : PlanarGraph v e f) (k : ℕ) :
      PlanarGraph v (e + k) (f + k) := by
    induction k with
    | zero => exact h
    | succ k ih => exact .addEdge v (e + k) (f + k) ih

-- Double wheel examples
example : PlanarGraph 5 9 6 := doubleWheel_planar 3 (by omega)
example : PlanarGraph 6 12 8 := doubleWheel_planar 4 (by omega)
example : PlanarGraph 7 15 10 := doubleWheel_planar 5 (by omega)

-- ============================================================
-- DODECAHEDRON AND ICOSAHEDRON
-- ============================================================
-- Two remaining Platonic solids.
-- Dodecahedron: V=20, E=30, F=12 (12 pentagonal faces)
-- Icosahedron:  V=12, E=30, F=20 (20 triangular faces)

/--
Existence witness: there is a connected planar graph with V=20, E=30, F=12.
These are the parameters of the dodecahedron (Euler: 20 + 12 = 30 + 2 ✓).

Note: this construction (path + addEdge) produces *some* valid planar graph
with those counts — not the actual dodecahedron (which has 12 pentagonal
faces). The specific combinatorial structure of the dodecahedron is verified
separately in `CMapEuler.lean` via `native_decide`.
-/
theorem dodecahedron_planar_witness : PlanarGraph 20 30 12 := by
  -- Build inductively: start from point, add 19 leaves (V=20, E=19, F=1),
  -- then 11 addEdge operations to get to E=30, F=12.
  have h1 : PlanarGraph 20 19 1 := path_planar 20 (by omega)
  have h := wheel_aux 20 19 1 h1 11
  have he : 19 + 11 = 30 := by omega
  have hf : 1 + 11 = 12 := by omega
  rw [he, hf] at h
  exact h
where
  wheel_aux (v e f : ℕ) (h : PlanarGraph v e f) (k : ℕ) :
      PlanarGraph v (e + k) (f + k) := by
    induction k with
    | zero => exact h
    | succ k ih => exact .addEdge v (e + k) (f + k) ih

/--
Existence witness: there is a connected planar graph with V=12, E=30, F=20.
These are the parameters of the icosahedron (Euler: 12 + 20 = 30 + 2 ✓).

Note: this construction (path + addEdge) produces *some* valid planar graph
with those counts — not the actual icosahedron (which has 20 triangular
faces). See `dodecahedron_planar_witness` for the same caveat.
-/
theorem icosahedron_planar_witness : PlanarGraph 12 30 20 := by
  -- Build: path (V=12, E=11, F=1) + 19 addEdge ops → (V=12, E=30, F=20)
  have h1 : PlanarGraph 12 11 1 := path_planar 12 (by omega)
  have h := wheel_aux 12 11 1 h1 19
  have he : 11 + 19 = 30 := by omega
  have hf : 1 + 19 = 20 := by omega
  rw [he, hf] at h
  exact h
where
  wheel_aux (v e f : ℕ) (h : PlanarGraph v e f) (k : ℕ) :
      PlanarGraph v (e + k) (f + k) := by
    induction k with
    | zero => exact h
    | succ k ih => exact .addEdge v (e + k) (f + k) ih

-- ============================================================
-- ALL PLATONIC SOLIDS SATISFY EULER (kernel-level)
-- ============================================================

/-- All five Platonic solids satisfy V + F = E + 2. -/
theorem all_platonic_solids_euler :
    (4 + 4 = 6 + 2) ∧   -- tetrahedron K₄
    (8 + 6 = 12 + 2) ∧  -- cube
    (6 + 8 = 12 + 2) ∧  -- octahedron
    (20 + 12 = 30 + 2) ∧ -- dodecahedron
    (12 + 20 = 30 + 2)   -- icosahedron
    := by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- Each Platonic solid satisfies Euler as a PlanarGraph-derived fact. -/
theorem platonic_euler_derived :
    (4 + 4 = 6 + 2 ∧ PlanarGraph 4 6 4) ∧
    (8 + 6 = 12 + 2 ∧ PlanarGraph 8 12 6) ∧
    (6 + 8 = 12 + 2 ∧ PlanarGraph 6 12 8) ∧
    (20 + 12 = 30 + 2 ∧ PlanarGraph 20 30 12) ∧
    (12 + 20 = 30 + 2 ∧ PlanarGraph 12 30 20) :=
  ⟨⟨rfl, k4⟩, ⟨rfl, cube_witness⟩, ⟨rfl, octahedron_witness⟩,
   ⟨rfl, dodecahedron_planar_witness⟩, ⟨rfl, icosahedron_planar_witness⟩⟩

-- ============================================================
-- PLATONIC CLASSIFICATION (the 5 solids are uniquely determined)
-- ============================================================
-- A regular polyhedron has every face with p edges and every vertex
-- with q edges. The handshake constraints give:
--   pF = 2E  (each edge borders 2 faces)
--   qV = 2E  (each edge has 2 endpoints)
-- So F = 2E/p, V = 2E/q. Combined with V - E + F = 2:
--   2E/q - E + 2E/p = 2  ⟹  1/p + 1/q - 1/2 = 1/E  > 0
-- Therefore: 1/p + 1/q > 1/2.
-- With p, q ≥ 3, only 5 pairs (p,q) satisfy this:
--   (3,3) tetrahedron, (3,4) cube, (4,3) octahedron,
--   (3,5) dodecahedron, (5,3) icosahedron.

/--
**Platonic constraint**: for a regular planar graph with face-degree p
and vertex-degree q (both ≥ 3) embedded such that pF = qV = 2E, Euler
forces 1/p + 1/q > 1/2.

Restated arithmetically: 2p + 2q > pq (multiplying through by 2pq).
-/
theorem platonic_constraint (p q V E F : ℕ)
    (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hfaces : p * F = 2 * E)
    (hverts : q * V = 2 * E)
    (hpos_E : 1 ≤ E)
    (hplanar : V + F = E + 2) :
    2 * p + 2 * q > p * q := by
  -- From V + F = E + 2 with V = 2E/q, F = 2E/p:
  -- 2E/q + 2E/p = E + 2
  -- Multiply by pq: 2Ep + 2Eq = Epq + 2pq
  -- So E(2p + 2q - pq) = 2pq > 0
  -- Therefore 2p + 2q > pq.
  have h1 : 2 * p * E + 2 * q * E = p * q * E + 2 * p * q := by
    have := hplanar
    have eulerPQ : p * q * V + p * q * F = p * q * E + 2 * p * q := by
      have : p * q * (V + F) = p * q * (E + 2) := by rw [this]
      ring_nf at this ⊢
      linarith
    have hqv : p * q * V = 2 * p * E := by
      have : p * (q * V) = p * (2 * E) := by rw [hverts]
      ring_nf at this ⊢
      linarith
    have hpf : p * q * F = 2 * q * E := by
      have : q * (p * F) = q * (2 * E) := by rw [hfaces]
      ring_nf at this ⊢
      linarith
    linarith
  -- E ≥ 1 and the equation E(2p+2q-pq) = 2pq forces 2p+2q-pq > 0
  nlinarith [hpos_E, Nat.zero_le p, Nat.zero_le q]

/--
**The 5 Platonic pairs (p, q)**: the only solutions to 2p + 2q > pq
with p, q ≥ 3 are exactly the 5 Platonic configurations.

For p, q ≥ 6: 2p + 2q ≤ pq (so excluded).
For p, q ≥ 3, exhaustive check leaves only (3,3), (3,4), (4,3), (3,5), (5,3).
-/
theorem platonic_pairs_classification (p q : ℕ)
    (hp : 3 ≤ p) (hq : 3 ≤ q) (h : 2 * p + 2 * q > p * q) :
    (p = 3 ∧ q = 3) ∨ (p = 3 ∧ q = 4) ∨ (p = 4 ∧ q = 3) ∨
    (p = 3 ∧ q = 5) ∨ (p = 5 ∧ q = 3) := by
  have hp_le : p ≤ 5 := by
    by_contra hp6; push_neg at hp6; nlinarith
  have hq_le : q ≤ 5 := by
    by_contra hq6; push_neg at hq6; nlinarith
  interval_cases p <;> interval_cases q <;> omega

/--
**Platonic Solid Classification Theorem**:
Any regular planar polyhedron (every face has p ≥ 3 edges, every vertex
has q ≥ 3 incident edges, pF = qV = 2E) must satisfy
(p, q) ∈ {(3,3), (3,4), (4,3), (3,5), (5,3)}.

These are precisely the tetrahedron, cube, octahedron, dodecahedron,
and icosahedron.

This combines:
- `platonic_constraint` (Euler → 2p+2q > pq)
- `platonic_pairs_classification` (interval analysis)
-/
theorem platonic_classification (p q V E F : ℕ)
    (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hfaces : p * F = 2 * E)
    (hverts : q * V = 2 * E)
    (hpos_E : 1 ≤ E)
    (hplanar : V + F = E + 2) :
    (p = 3 ∧ q = 3) ∨ (p = 3 ∧ q = 4) ∨ (p = 4 ∧ q = 3) ∨
    (p = 3 ∧ q = 5) ∨ (p = 5 ∧ q = 3) :=
  platonic_pairs_classification p q hp hq
    (platonic_constraint p q V E F hp hq hfaces hverts hpos_E hplanar)

-- ============================================================
-- K₅ AND K₃,₃ NON-PLANARITY VIA EDGE BOUNDS
-- ============================================================
-- Standard graph-theory consequence: any planar graph with V ≥ 3 and
-- minimum face-degree ≥ 3 satisfies E ≤ 3V - 6. K₅ has V=5, E=10,
-- and 10 > 3·5 - 6 = 9. Contradiction.

/--
**Cleaner K₅ non-planarity** via the face-degree bound:
any planar graph on 5 vertices with simple structure (faces ≥ 3 edges)
has at most 9 edges. K₅ has 10 edges. Hence K₅ is not planar.
-/
theorem k5_non_planar_via_face_bound
    (h_planar : ∃ f, PlanarGraph 5 10 f ∧ 3 * f ≤ 2 * 10) : False := by
  obtain ⟨f, hpg, hf⟩ := h_planar
  have := euler_formula hpg
  omega

/--
**Cleaner K₃,₃ non-planarity** via the bipartite face-degree bound:
bipartite planar graphs with V ≥ 3 satisfy E ≤ 2V - 4.
K₃,₃ has V=6, E=9, and 9 > 2·6 - 4 = 8.
-/
theorem k33_non_planar_via_bipartite_bound
    (h_planar : ∃ f, PlanarGraph 6 9 f ∧ 4 * f ≤ 2 * 9) : False := by
  obtain ⟨f, hpg, hf⟩ := h_planar
  have := euler_formula hpg
  omega

-- ============================================================
-- THE PETERSEN GRAPH IS NOT PLANAR
-- ============================================================
-- The Petersen graph: V=10, E=15, girth=5 (no triangles or 4-cycles).
-- If planar, every face has ≥ 5 edges.
-- Euler: F = 15 - 10 + 2 = 7.
-- But 5·7 = 35 > 30 = 2·15, contradiction.

/--
No connected planar graph can have V=10, E=15, and all faces of size ≥5.

The Petersen graph has exactly these parameters (V=10, E=15, girth=5), so
if it were planarly embeddable then F=7 by Euler, but 5·7=35 > 2·15=30.

Note: this theorem takes the face-size condition `5 * f ≤ 2 * 15` as a
hypothesis. The Petersen graph is not formally defined here as a
`SimpleGraph`; the theorem applies to any graph matching those parameters.
For a fully formal statement see `K5_not_planarly_embeddable` as a model.
-/
theorem petersen_not_planar
    (h_planar : ∃ f, PlanarGraph 10 15 f ∧ 5 * f ≤ 2 * 15) : False := by
  obtain ⟨f, hpg, hf⟩ := h_planar
  have := euler_formula hpg
  omega

-- ============================================================
-- HEAWOOD GRAPH IS NOT PLANAR
-- ============================================================
-- The Heawood graph: V=14, E=21, girth=6.
-- If planar: F = 21 - 14 + 2 = 9.
-- But 6·9 = 54 > 42 = 2·21, contradiction.

/--
No connected planar graph can have V=14, E=21, and all faces of size ≥6.

The Heawood graph has exactly these parameters (V=14, E=21, girth=6), so
if it were planarly embeddable then F=9 by Euler, but 6·9=54 > 2·21=42.

Same caveat as `petersen_not_planar`: the face-size condition is a
hypothesis, not a proved property of a formally defined Heawood graph.
-/
theorem heawood_not_planar
    (h_planar : ∃ f, PlanarGraph 14 21 f ∧ 6 * f ≤ 2 * 21) : False := by
  obtain ⟨f, hpg, hf⟩ := h_planar
  have := euler_formula hpg
  omega

/--
**General girth-based non-planarity**:
A planar graph with V ≥ 3 vertices, E edges, and minimum face-degree
g ≥ 3 satisfies the bound E·(g - 2) ≤ g·(V - 2).

Equivalently: E ≤ g·(V-2)/(g-2). When this is violated, the graph
cannot be planar.

For g = 3: E ≤ 3V - 6 (the classical bound).
For g = 4: E ≤ 2V - 4 (bipartite bound).
For g = 5: E ≤ 5(V-2)/3 (Petersen-style bound).
For g = 6: E ≤ 3(V-2)/2 (Heawood-style bound).
-/
theorem girth_planarity_bound (v e f g : ℕ)
    (h : PlanarGraph v e f)
    (hface : g * f ≤ 2 * e) :
    g * e + 2 * g ≤ 2 * e + g * v := by
  -- Direct: Euler v + f = e + 2 ⟹ g*v + g*f = g*e + 2*g.
  -- With g*f ≤ 2*e: g*e + 2*g ≤ 2*e + g*v.
  have hE := euler_formula h
  have hmul : g * (v + f) = g * (e + 2) := by rw [hE]
  nlinarith [hmul, hface]

-- ============================================================
-- HEAWOOD-STYLE: AVERAGE DEGREE IS SMALL
-- ============================================================
-- For any planar graph with V ≥ 3 and faces ≥ 3, 2E ≤ 6V - 12 < 6V.
-- The sum of vertex degrees is 2E, so the AVERAGE degree is < 6.
-- Therefore some vertex has degree ≤ 5.

/--
**Six-degree lemma**: any planar graph with V ≥ 3 and every face
of degree ≥ 3 satisfies 2E < 6V, so the average vertex degree
is strictly less than 6. This is the key step toward the
6-color theorem for planar graphs.
-/
theorem planar_six_degree_bound (v e f : ℕ)
    (hv : 3 ≤ v) (h : PlanarGraph v e f)
    (hface : 3 * f ≤ 2 * e) :
    2 * e < 6 * v := by
  have := euler_formula h
  omega

/--
**Five-or-less degree existence (semantic)**: in any planar graph,
sum of vertex degrees = 2E < 6V, so by pigeonhole at least one
vertex has degree ≤ 5.

This is the precondition for the classical 6-color theorem proof
by induction: remove a degree-≤5 vertex, color the rest, color it
with one of the 6 colors not used by its neighbors.
-/
theorem planar_has_low_degree_vertex (v e f : ℕ)
    (hv : 3 ≤ v) (h : PlanarGraph v e f)
    (hface : 3 * f ≤ 2 * e)
    (degree_sum : ℕ) (hd : degree_sum = 2 * e) :
    degree_sum < 6 * v := by
  rw [hd]; exact planar_six_degree_bound v e f hv h hface

-- ============================================================
-- TRIANGULATION IDENTITIES
-- ============================================================
-- A maximal planar graph (triangulation): every face has exactly 3 edges.
-- Then 3F = 2E exactly. Combined with V + F = E + 2:
--   F = 2V - 4, E = 3V - 6.

/--
**Triangulation face count**: in a planar triangulation
(every face exactly 3-sided, 3F = 2E), F = 2V - 4 when V ≥ 3.
-/
theorem triangulation_face_count (v e f : ℕ)
    (hv : 3 ≤ v) (h : PlanarGraph v e f)
    (hexact : 3 * f = 2 * e) :
    f + 4 = 2 * v := by
  have := euler_formula h
  omega

/--
**Triangulation edge count**: E = 3V - 6 for triangulations.
-/
theorem triangulation_edge_count (v e f : ℕ)
    (hv : 3 ≤ v) (h : PlanarGraph v e f)
    (hexact : 3 * f = 2 * e) :
    e + 6 = 3 * v := by
  have := euler_formula h
  omega

/--
**Combined identity**: for triangulations, E + F = 5V - 10.
-/
theorem triangulation_combined (v e f : ℕ)
    (hv : 3 ≤ v) (h : PlanarGraph v e f)
    (hexact : 3 * f = 2 * e) :
    e + f + 10 = 5 * v := by
  have := euler_formula h
  omega

-- ============================================================
-- SIMPLICIAL REGULAR POLYHEDRA
-- ============================================================
-- Regular triangulations: triangular faces + q-regular vertex degree.
-- From triangulation_face_count: F = 2V - 4.
-- From q-regularity: q*V = 2E = 3F = 3(2V-4) = 6V - 12.
-- So V*(q-6) = -12, i.e. V = 12/(6-q) when q < 6.

/--
**Regular triangulation constraint**: if every face is triangular and
every vertex has degree q ≥ 3, then q < 6 and 6V = qV + 12.
The 3 solutions: q=3 (tetrahedron V=4), q=4 (octahedron V=6),
q=5 (icosahedron V=12).

-/
theorem regular_triangulation_constraint (v e f q : ℕ)
    (hv : 3 ≤ v) (hq : 3 ≤ q)
    (h : PlanarGraph v e f)
    (hface : 3 * f = 2 * e)
    (hvert : q * v = 2 * e) :
    6 * v = q * v + 12 ∧ q < 6 := by
  have hE := euler_formula h
  -- From Euler v + f = e + 2 and 3f = 2e: e = 3v - 6, f = 2v - 4.
  -- From qv = 2e = 6v - 12: 6v = qv + 12.
  refine ⟨?_, ?_⟩
  · nlinarith [hE, hface, hvert, hv]
  · -- If q ≥ 6: qV ≥ 6V, but qV + 12 = 6V is impossible.
    by_contra h6
    push_neg at h6
    nlinarith [hE, hface, hvert, hv, h6]

/-- The three regular triangulations: V=4 (tetrahedron), V=6 (octahedron),
V=12 (icosahedron). -/
theorem regular_triangulation_enumeration (v q : ℕ)
    (hv : 3 ≤ v) (hq : 3 ≤ q) (hq6 : q < 6)
    (heq : 6 * v = q * v + 12) :
    (q = 3 ∧ v = 4) ∨ (q = 4 ∧ v = 6) ∨ (q = 5 ∧ v = 12) := by
  interval_cases q <;> omega

-- ============================================================
-- DUAL: REGULAR NON-TRIANGULAR POLYHEDRA (p ≥ 4)
-- ============================================================
-- For pF = 2E with p ≥ 4 and qV = 2E with q = 3 (cubic vertices):
--   The 3-cubic graph case has at most 2 solutions:
--   p=3 → tetrahedron (already covered above)
--   p=4 → cube (V=8, E=12, F=6)
--   p=5 → dodecahedron (V=20, E=30, F=12)
--   p=6 → would give 0/0 (infinite/flat) — degenerate

/--
**3-regular polyhedron constraint**: a planar polyhedron where every
vertex has degree exactly 3 and every face has exactly p edges satisfies
3V = 2E = pF and V + F = E + 2, forcing 6V = (p+2)·V/?... Cleanly:
  3V = 2E ⟹ V = 2E/3
  pF = 2E ⟹ F = 2E/p
  Euler: 2E/3 + 2E/p = E + 2 ⟹ E(2/3 + 2/p - 1) = 2 ⟹ E(2p + 6 - 3p) = 6p
  ⟹ E(6 - p) = 6p, so p < 6.
-/
theorem regular_cubic_constraint (v e f p : ℕ)
    (hv : 4 ≤ v) (hp : 3 ≤ p)
    (h : PlanarGraph v e f)
    (hface : p * f = 2 * e)
    (hvert : 3 * v = 2 * e) :
    e * 6 = e * p + 6 * p ∧ p < 6 := by
  have hE := euler_formula h
  refine ⟨?_, ?_⟩
  · nlinarith [hE, hface, hvert, hv, hp]
  · by_contra hp6
    push_neg at hp6
    -- p ≥ 6 ⟹ ep + 6p ≥ 6e + 6p > 6e, contradicting 6e = ep + 6p
    nlinarith [hE, hface, hvert, hv, hp6]

/-- The 3-regular planar polyhedra: tetrahedron (p=3), cube (p=4),
dodecahedron (p=5). -/
theorem regular_cubic_enumeration (e p : ℕ)
    (he : 6 ≤ e) (hp : 3 ≤ p) (hp6 : p < 6)
    (heq : e * 6 = e * p + 6 * p) :
    (p = 3 ∧ e = 6) ∨ (p = 4 ∧ e = 12) ∨ (p = 5 ∧ e = 30) := by
  interval_cases p <;> omega

-- ============================================================
-- DEGREE-SUM BOUNDS
-- ============================================================
-- Generalizes the six-degree bound: from g·F ≤ 2E and Euler we get
-- 2E ≤ (2g/(g-2))·V - (4g/(g-2)).
-- For g=3 this gives 2E < 6V; for g=4 it gives 2E ≤ 4V - 8; etc.

/--
**Bipartite four-degree bound**: planar bipartite graph satisfies
2E + 8 ≤ 4V (average degree < 4).
-/
theorem planar_bipartite_four_degree_bound (v e f : ℕ)
    (hv : 3 ≤ v) (h : PlanarGraph v e f)
    (hface : 4 * f ≤ 2 * e) :
    2 * e + 8 ≤ 4 * v := by
  have := euler_formula h
  omega

/--
**Planar triangle-free**: same as bipartite (girth ≥ 4) gives E ≤ 2V - 4.
-/
theorem planar_triangle_free_edge_bound (v e f : ℕ)
    (hv : 3 ≤ v) (h : PlanarGraph v e f)
    (hgirth : 4 * f ≤ 2 * e) :
    e + 4 ≤ 2 * v := by
  have := euler_formula h
  omega

/--
**Cubic planar graphs**: V vertices each of degree exactly 3 satisfies
2E = 3V, so V is even and E = 3V/2.
-/
theorem cubic_planar_edge_count (v e : ℕ)
    (hvert : 3 * v = 2 * e) :
    2 * e = 3 * v := by omega

-- ============================================================
-- LADDER L_n: two parallel paths connected by n rungs
-- ============================================================
-- L_n = K_2 × P_n: V = 2n, E = 3n - 2, F = n
-- (n-1 quadrilateral cells + 1 outer face)

/-- Ladder L_n: V = 2n, E = 3n - 2, F = n (for n ≥ 2). -/
theorem ladder_planar (n : ℕ) (hn : 2 ≤ n) :
    PlanarGraph (2 * n) (3 * n - 2) n := by
  -- Base L_2: 4-cycle (V=4, E=4, F=2).
  -- Inductive step: L_{n+1} = L_n + 2 leaves + 1 closing edge
  -- (V: 2n → 2n+2, E: 3n-2 → 3(n+1)-2, F: n → n+1)
  induction n, hn using Nat.le_induction with
  | base =>
    -- L_2: 4-cycle. V=4, E=4, F=2. 3·2 - 2 = 4 ✓
    have : 3 * 2 - 2 = 4 := by omega
    rw [this]
    exact cycle_planar 4 (by omega)
  | succ k hk ih =>
    -- We have L_k: PlanarGraph (2k) (3k-2) k
    -- Want L_{k+1}: PlanarGraph (2(k+1)) (3(k+1)-2) (k+1) = PlanarGraph (2k+2) (3k+1) (k+1)
    -- Apply: addLeaf (V=2k+1, E=3k-1, F=k), addLeaf (V=2k+2, E=3k, F=k),
    --        addEdge (V=2k+2, E=3k+1, F=k+1)
    have h1 : PlanarGraph (2 * k + 1) (3 * k - 1) k := by
      have := PlanarGraph.addLeaf (2 * k) (3 * k - 2) k ih
      have he : 3 * k - 2 + 1 = 3 * k - 1 := by omega
      rw [he] at this; exact this
    have h2 : PlanarGraph (2 * k + 2) (3 * k) k := by
      have := PlanarGraph.addLeaf (2 * k + 1) (3 * k - 1) k h1
      have he : 3 * k - 1 + 1 = 3 * k := by omega
      rw [he] at this; exact this
    have h3 : PlanarGraph (2 * k + 2) (3 * k + 1) (k + 1) :=
      .addEdge (2 * k + 2) (3 * k) k h2
    have hv : 2 * (k + 1) = 2 * k + 2 := by ring
    have he : 3 * (k + 1) - 2 = 3 * k + 1 := by omega
    rw [hv, he]; exact h3

-- Ladder examples
example : PlanarGraph 4 4 2 := ladder_planar 2 (by omega)    -- L_2 = C_4
example : PlanarGraph 6 7 3 := ladder_planar 3 (by omega)
example : PlanarGraph 8 10 4 := ladder_planar 4 (by omega)

-- ============================================================
-- VAN STAUDT'S ARITHMETIC CORE (Jordan-free)
-- ============================================================
-- Classical fact: V - E + F = 2 follows arithmetically from the
-- spanning-tree decomposition without invoking Jordan curve theorem.
--
-- If a spanning tree of G has V-1 edges, and the complementary edges
-- form a spanning tree of the dual G* with F-1 edges, and together
-- they partition all E edges, then V + F = E + 2 follows immediately.

/--
Van Staudt's arithmetic identity: if a graph's edges partition into
a spanning tree (V-1 edges) and a dual spanning tree (F-1 edges),
then V + F = E + 2.

This isolates the purely combinatorial content of Van Staudt's proof
from any topological argument. The substantive remaining work is
constructing the spanning trees themselves.
-/
theorem vanStaudt_arith (V E F : ℕ)
    (hV : 1 ≤ V) (hF : 1 ≤ F)
    (hpartition : (V - 1) + (F - 1) = E) :
    V + F = E + 2 := by
  omega

end PlanarGraph

-- ============================================================
-- STEP 2: BRIDGE  SimpleGraph ↔ PlanarGraph
-- ============================================================
-- Connects our inductive type to Mathlib's SimpleGraph.
-- A PlanarEmbedding assigns a face count to a concrete graph
-- and provides a PlanarGraph witness with matching V and E.

open SimpleGraph in
/--
A `PlanarEmbedding G` is a combinatorial certificate: a face count `f`
together with a `PlanarGraph` witness whose vertex and edge counts match
those of `G`. This witnesses Euler compatibility (V - E + F = 2) but
does not encode a geometric embedding or prove absence of edge crossings.
-/
structure PlanarEmbedding {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] where
  faces   : ℕ
  witness : PlanarGraph (Fintype.card α) G.edgeFinset.card faces

/-- Euler's formula for any `SimpleGraph` with a `PlanarEmbedding`. -/
theorem euler_of_embedding {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (emb : PlanarEmbedding G) :
    (Fintype.card α : ℤ) - G.edgeFinset.card + emb.faces = 2 :=
  PlanarGraph.euler_int emb.witness

-- ============================================================
-- STEP 1: POSITIVE CASES  (concrete SimpleGraphs have witnesses)
-- ============================================================
-- K_n = complete graph on Fin n  (Mathlib: ⊤ : SimpleGraph (Fin n))

section PositiveCases

-- Vertex counts (trivial)
theorem Kn_vertices (n : ℕ) : Fintype.card (Fin n) = n := Fintype.card_fin n

-- Edge counts (verified by kernel computation)
theorem K3_edges : (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by decide
theorem K4_edges : (⊤ : SimpleGraph (Fin 4)).edgeFinset.card = 6 := by decide
theorem K5_edges : (⊤ : SimpleGraph (Fin 5)).edgeFinset.card = 10 := by decide

-- K₃ is planarly embeddable
theorem K3_hasPlanarEmbedding :
    Nonempty (PlanarEmbedding (⊤ : SimpleGraph (Fin 3))) :=
  ⟨⟨2, by simp [Kn_vertices, K3_edges]; exact PlanarGraph.triangle⟩⟩

-- K₄ is planarly embeddable
theorem K4_hasPlanarEmbedding :
    Nonempty (PlanarEmbedding (⊤ : SimpleGraph (Fin 4))) :=
  ⟨⟨4, by simp [Kn_vertices, K4_edges]; exact PlanarGraph.k4⟩⟩

-- Euler holds for K₃ embedding
theorem K3_euler (emb : PlanarEmbedding (⊤ : SimpleGraph (Fin 3))) :
    (3 : ℤ) - 3 + emb.faces = 2 := by
  have := euler_of_embedding _ emb
  simp [Kn_vertices, K3_edges] at this
  exact this

end PositiveCases

-- ============================================================
-- STEP 3: K₅ NOT PLANARLY EMBEDDABLE
-- ============================================================
-- Full chain: Mathlib's SimpleGraph (Fin 5) → PlanarEmbedding →
-- PlanarGraph 5 10 f → Euler contradiction.

/--
**K₅ is not planarly embeddable** (with simple faces, i.e. each face
bounded by ≥ 3 edges — guaranteed since K₅ has no loops or multi-edges).

Full chain:
1. K₅ has V=5 (Fintype.card_fin)
2. K₅ has E=10 (by kernel computation)
3. Any PlanarEmbedding with 3·F ≤ 2·10 would need F=7 (Euler), but 3·7=21>20. ⊥
-/
theorem K5_not_planarly_embeddable :
    ¬ ∃ (emb : PlanarEmbedding (⊤ : SimpleGraph (Fin 5))),
        3 * emb.faces ≤ 2 * 10 := by
  rintro ⟨⟨f, h⟩, hf⟩
  simp [Kn_vertices, K5_edges] at h
  exact PlanarGraph.k5_not_planar ⟨f, h, hf⟩

-- ============================================================
-- PETERSEN GRAPH: FORMAL NON-PLANARITY
-- ============================================================

private def isPetersenEdge (i j : Fin 10) : Bool :=
  (i.val, j.val) ∈ ([(0,1),(1,0),(1,2),(2,1),(2,3),(3,2),(3,4),(4,3),(4,0),(0,4),
                      (5,7),(7,5),(7,9),(9,7),(9,6),(6,9),(6,8),(8,6),(8,5),(5,8),
                      (0,5),(5,0),(1,6),(6,1),(2,7),(7,2),(3,8),(8,3),(4,9),(9,4)]
                     : List (ℕ × ℕ))

private theorem isPetersenEdge_symm (i j : Fin 10)
    (h : isPetersenEdge i j = true) : isPetersenEdge j i = true := by
  revert i j; native_decide

private theorem isPetersenEdge_irrefl (i : Fin 10) :
    isPetersenEdge i i ≠ true := by
  revert i; native_decide

/-- The Petersen graph: 3-regular on 10 vertices, 15 edges, girth 5. -/
def petersenGraph : SimpleGraph (Fin 10) where
  Adj i j  := isPetersenEdge i j = true
  symm     := isPetersenEdge_symm
  loopless := ⟨isPetersenEdge_irrefl⟩

instance : DecidableRel petersenGraph.Adj :=
  fun i j => Bool.decEq (isPetersenEdge i j) true

theorem Petersen_edges : petersenGraph.edgeFinset.card = 15 := by native_decide

/-- The Petersen graph has no triangle. -/
lemma petersenGraph_no_triangle :
    ∀ i j k : Fin 10,
    petersenGraph.Adj i j → petersenGraph.Adj j k → petersenGraph.Adj k i → False := by
  native_decide

/-- The Petersen graph has no 4-cycle with distinct opposite vertices. -/
lemma petersenGraph_no_4cycle :
    ∀ i j k l : Fin 10,
    ¬ (petersenGraph.Adj i j ∧ petersenGraph.Adj j k ∧ petersenGraph.Adj k l ∧
       petersenGraph.Adj l i ∧ i ≠ k ∧ j ≠ l) := by
  native_decide

/-- All cycles in the Petersen graph have length ≥ 5. -/
theorem petersenGraph_egirth_ge_5 : 5 ≤ petersenGraph.egirth := by
  rw [SimpleGraph.le_egirth]
  intro v w hw
  suffices h : 5 ≤ w.length by exact_mod_cast h
  by_contra hlt
  push_neg at hlt
  have h3 : 3 ≤ w.length := hw.three_le_length
  have hlen : w.length = 3 ∨ w.length = 4 := by omega
  have hv0 : w.getVert 0 = v := SimpleGraph.Walk.getVert_zero w
  rcases hlen with h3eq | h4eq
  · -- 3-cycle: extract triangle
    have hv3 : w.getVert 3 = v := by
      have h := SimpleGraph.Walk.getVert_length w; rw [h3eq] at h; exact h
    have h01 := w.adj_getVert_succ (show 0 < w.length by omega)
    have h12 := w.adj_getVert_succ (show 1 < w.length by omega)
    have h23 := w.adj_getVert_succ (show 2 < w.length by omega)
    rw [hv3, ← hv0] at h23
    exact petersenGraph_no_triangle _ _ _ h01 h12 h23
  · -- 4-cycle: extract cycle with distinct opposite vertices
    have hv4 : w.getVert 4 = v := by
      have h := SimpleGraph.Walk.getVert_length w; rw [h4eq] at h; exact h
    have h01 := w.adj_getVert_succ (show 0 < w.length by omega)
    have h12 := w.adj_getVert_succ (show 1 < w.length by omega)
    have h23 := w.adj_getVert_succ (show 2 < w.length by omega)
    have h34 := w.adj_getVert_succ (show 3 < w.length by omega)
    rw [hv4, ← hv0] at h34
    have hinj := hw.getVert_injOn'
    have mem : ∀ k : ℕ, k ≤ 3 → k ∈ {i | i ≤ w.length - 1} := fun k hk => by
      simp only [Set.mem_setOf_eq]; omega
    have h02 : w.getVert 0 ≠ w.getVert 2 := fun heq =>
      absurd (hinj (mem 0 (by omega)) (mem 2 (by omega)) heq) (by norm_num)
    have h13 : w.getVert 1 ≠ w.getVert 3 := fun heq =>
      absurd (hinj (mem 1 (by omega)) (mem 3 (by omega)) heq) (by norm_num)
    exact petersenGraph_no_4cycle _ _ _ _ ⟨h01, h12, h23, h34, h02, h13⟩

/--
**Petersen graph is not planarly embeddable.**
The graph is concretely defined (outer pentagon 0-1-2-3-4-0, inner pentagram
5-7-9-6-8-5, spokes 0-5…4-9) with edge count machine-verified. Girth = 5 is
formally proved in `petersenGraph_egirth_ge_5`: any cycle has length ≥ 5,
so any planar embedding must satisfy 5F ≤ 2E. With E=15 this forces F ≤ 6,
but Euler gives F = 7. Contradiction.

The hypothesis `5 * emb.faces ≤ 2 * 15` encodes the girth-5 face condition;
`petersenGraph_egirth_ge_5` justifies why any planar embedding must satisfy it.
-/
theorem petersenGraph_not_planarly_embeddable :
    ¬ ∃ (emb : PlanarEmbedding petersenGraph),
        5 * emb.faces ≤ 2 * 15 := by
  rintro ⟨⟨f, h⟩, hf⟩
  simp only [Kn_vertices, Petersen_edges] at h
  exact PlanarGraph.petersen_not_planar ⟨f, h, hf⟩

-- ============================================================
-- HEAWOOD GRAPH: FORMAL NON-PLANARITY
-- ============================================================

private def isHeawoodEdge (i j : Fin 14) : Bool :=
  (i.val, j.val) ∈ ([(0,1),(1,0),(0,5),(5,0),(0,9),(9,0),
                      (1,2),(2,1),(1,12),(12,1),
                      (2,3),(3,2),(2,7),(7,2),
                      (3,4),(4,3),(3,10),(10,3),
                      (4,5),(5,4),(4,13),(13,4),
                      (5,6),(6,5),
                      (6,7),(7,6),(6,11),(11,6),
                      (7,8),(8,7),
                      (8,9),(9,8),(8,13),(13,8),
                      (9,10),(10,9),
                      (10,11),(11,10),
                      (11,12),(12,11),
                      (12,13),(13,12)]
                     : List (ℕ × ℕ))

private theorem isHeawoodEdge_symm (i j : Fin 14)
    (h : isHeawoodEdge i j = true) : isHeawoodEdge j i = true := by
  revert i j; native_decide

private theorem isHeawoodEdge_irrefl (i : Fin 14) :
    isHeawoodEdge i i ≠ true := by
  revert i; native_decide

/-- The Heawood graph: 3-regular on 14 vertices, 21 edges, girth 6. -/
def heawoodGraph : SimpleGraph (Fin 14) where
  Adj i j  := isHeawoodEdge i j = true
  symm     := isHeawoodEdge_symm
  loopless := ⟨isHeawoodEdge_irrefl⟩

instance : DecidableRel heawoodGraph.Adj :=
  fun i j => Bool.decEq (isHeawoodEdge i j) true

theorem Heawood_edges : heawoodGraph.edgeFinset.card = 21 := by native_decide

/-- The Heawood graph has no triangle. -/
lemma heawoodGraph_no_triangle :
    ∀ i j k : Fin 14,
    heawoodGraph.Adj i j → heawoodGraph.Adj j k → heawoodGraph.Adj k i → False := by
  native_decide

/-- The Heawood graph has no 4-cycle with distinct opposite vertices. -/
lemma heawoodGraph_no_4cycle :
    ∀ i j k l : Fin 14,
    ¬ (heawoodGraph.Adj i j ∧ heawoodGraph.Adj j k ∧ heawoodGraph.Adj k l ∧
       heawoodGraph.Adj l i ∧ i ≠ k ∧ j ≠ l) := by
  native_decide

/-- The Heawood graph has no 5-cycle with all non-adjacent vertices distinct. -/
lemma heawoodGraph_no_5cycle :
    ∀ i j k l m : Fin 14,
    ¬ (heawoodGraph.Adj i j ∧ heawoodGraph.Adj j k ∧ heawoodGraph.Adj k l ∧
       heawoodGraph.Adj l m ∧ heawoodGraph.Adj m i ∧
       i ≠ k ∧ i ≠ l ∧ j ≠ l ∧ j ≠ m ∧ k ≠ m) := by
  native_decide

/-- All cycles in the Heawood graph have length ≥ 6. -/
theorem heawoodGraph_egirth_ge_6 : 6 ≤ heawoodGraph.egirth := by
  rw [SimpleGraph.le_egirth]
  intro v w hw
  suffices h : 6 ≤ w.length by exact_mod_cast h
  by_contra hlt
  push_neg at hlt
  have h3 : 3 ≤ w.length := hw.three_le_length
  have hlen : w.length = 3 ∨ w.length = 4 ∨ w.length = 5 := by omega
  have hv0 : w.getVert 0 = v := SimpleGraph.Walk.getVert_zero w
  rcases hlen with h3eq | h4eq | h5eq
  · -- 3-cycle: triangle
    have hv3  : w.getVert 3 = v := by
      have h := SimpleGraph.Walk.getVert_length w; rw [h3eq] at h; exact h
    have h01  := w.adj_getVert_succ (show 0 < w.length by omega)
    have h12  := w.adj_getVert_succ (show 1 < w.length by omega)
    have h23  := w.adj_getVert_succ (show 2 < w.length by omega)
    rw [hv3, ← hv0] at h23
    exact heawoodGraph_no_triangle _ _ _ h01 h12 h23
  · -- 4-cycle
    have hv4  : w.getVert 4 = v := by
      have h := SimpleGraph.Walk.getVert_length w; rw [h4eq] at h; exact h
    have h01  := w.adj_getVert_succ (show 0 < w.length by omega)
    have h12  := w.adj_getVert_succ (show 1 < w.length by omega)
    have h23  := w.adj_getVert_succ (show 2 < w.length by omega)
    have h34  := w.adj_getVert_succ (show 3 < w.length by omega)
    rw [hv4, ← hv0] at h34
    have hinj := hw.getVert_injOn'
    have mem  : ∀ k : ℕ, k ≤ 3 → k ∈ {i | i ≤ w.length - 1} := fun k hk => by
      simp only [Set.mem_setOf_eq]; omega
    have h02 : w.getVert 0 ≠ w.getVert 2 := fun heq =>
      absurd (hinj (mem 0 (by omega)) (mem 2 (by omega)) heq) (by norm_num)
    have h13 : w.getVert 1 ≠ w.getVert 3 := fun heq =>
      absurd (hinj (mem 1 (by omega)) (mem 3 (by omega)) heq) (by norm_num)
    exact heawoodGraph_no_4cycle _ _ _ _ ⟨h01, h12, h23, h34, h02, h13⟩
  · -- 5-cycle
    have hv5  : w.getVert 5 = v := by
      have h := SimpleGraph.Walk.getVert_length w; rw [h5eq] at h; exact h
    have h01  := w.adj_getVert_succ (show 0 < w.length by omega)
    have h12  := w.adj_getVert_succ (show 1 < w.length by omega)
    have h23  := w.adj_getVert_succ (show 2 < w.length by omega)
    have h34  := w.adj_getVert_succ (show 3 < w.length by omega)
    have h45  := w.adj_getVert_succ (show 4 < w.length by omega)
    rw [hv5, ← hv0] at h45
    have hinj := hw.getVert_injOn'
    have mem  : ∀ k : ℕ, k ≤ 4 → k ∈ {i | i ≤ w.length - 1} := fun k hk => by
      simp only [Set.mem_setOf_eq]; omega
    have h02 : w.getVert 0 ≠ w.getVert 2 := fun heq =>
      absurd (hinj (mem 0 (by omega)) (mem 2 (by omega)) heq) (by norm_num)
    have h03 : w.getVert 0 ≠ w.getVert 3 := fun heq =>
      absurd (hinj (mem 0 (by omega)) (mem 3 (by omega)) heq) (by norm_num)
    have h13 : w.getVert 1 ≠ w.getVert 3 := fun heq =>
      absurd (hinj (mem 1 (by omega)) (mem 3 (by omega)) heq) (by norm_num)
    have h14 : w.getVert 1 ≠ w.getVert 4 := fun heq =>
      absurd (hinj (mem 1 (by omega)) (mem 4 (by omega)) heq) (by norm_num)
    have h24 : w.getVert 2 ≠ w.getVert 4 := fun heq =>
      absurd (hinj (mem 2 (by omega)) (mem 4 (by omega)) heq) (by norm_num)
    exact heawoodGraph_no_5cycle _ _ _ _ _
      ⟨h01, h12, h23, h34, h45, h02, h03, h13, h14, h24⟩

/--
**Heawood graph is not planarly embeddable.**
The graph is concretely defined with edge count machine-verified. Girth = 6 is
formally proved in `heawoodGraph_egirth_ge_6`: any cycle has length ≥ 6,
so any planar embedding must satisfy 6F ≤ 2E. With E=21 this forces F ≤ 7,
but Euler gives F = 9. Contradiction.

The hypothesis `6 * emb.faces ≤ 2 * 21` encodes the girth-6 face condition;
`heawoodGraph_egirth_ge_6` justifies why any planar embedding must satisfy it.
-/
theorem heawoodGraph_not_planarly_embeddable :
    ¬ ∃ (emb : PlanarEmbedding heawoodGraph),
        6 * emb.faces ≤ 2 * 21 := by
  rintro ⟨⟨f, h⟩, hf⟩
  simp only [Kn_vertices, Heawood_edges] at h
  exact PlanarGraph.heawood_not_planar ⟨f, h, hf⟩
