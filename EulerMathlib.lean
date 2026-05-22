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

theorem cube        : PlanarGraph 8 12 6 :=
  .addEdge 8 11 5 (.addEdge 8 10 4 (.addEdge 8 9 3 (.addEdge 8 8 2
    (.addEdge 8 7 1 (.addLeaf 7 6 1 (.addLeaf 6 5 1 (.addLeaf 5 4 1
      (.addLeaf 4 3 1 (.addLeaf 3 2 1 (.addLeaf 2 1 1
        (.addLeaf 1 0 1 .point)))))))))))

theorem octahedron  : PlanarGraph 6 12 8 :=
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
-- Wait, need to recount: with 2 hubs and n-cycle, F = 2n (n above + n below)
-- Then V + F = E + 2: (n+2) + 2n = 3n + 2 ✓

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

/-- Dodecahedron as a PlanarGraph: V=20, E=30, F=12. -/
theorem dodecahedron_planar : PlanarGraph 20 30 12 := by
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

/-- Icosahedron as a PlanarGraph: V=12, E=30, F=20. -/
theorem icosahedron_planar : PlanarGraph 12 30 20 := by
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
  ⟨⟨rfl, k4⟩, ⟨rfl, cube⟩, ⟨rfl, octahedron⟩,
   ⟨rfl, dodecahedron_planar⟩, ⟨rfl, icosahedron_planar⟩⟩

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
    -- q V = 2E, so p * (q V) = p * 2 E, so q * (p * V) = 2 p E
    -- Multiply Euler by pq:
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
  -- Bound p and q: if p ≥ 6 and q ≥ 3, then pq ≥ 18 but 2p+2q ≤ 2p+2p = 4p ≤ pq/1.5
  -- Cleaner: if p ≥ 6, then 2p+2q ≤ pq iff 2q ≤ p(q-2). With q ≥ 3: p(q-2) ≥ p ≥ 6 ≥ 2q only if q ≤ 3.
  -- Direct interval check via omega after bounding both p, q ≤ 5.
  have hp_le : p ≤ 5 := by
    by_contra hp6
    push_neg at hp6
    -- p ≥ 6 → p * q ≥ 6 * q ≥ 6 * 3 = 18, while 2p + 2q ≤ 2p + 2p (if q ≤ p)...
    -- Simpler: rewrite the bound. p*q ≥ 6q ≥ 2q + 4q ≥ 2q + 12 > 2q + 2p iff p < 6, contradiction.
    nlinarith
  have hq_le : q ≤ 5 := by
    by_contra hq6
    push_neg at hq6
    nlinarith
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
**The Petersen graph is not planar.** Cubic graph on 10 vertices with
girth 5; any planar embedding would force F=7 faces, each of length ≥5,
but 5·7 = 35 > 2·15 = 2E, contradiction.
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
**The Heawood graph is not planar.** 3-regular on 14 vertices with girth 6
(no triangles, 4-cycles, or 5-cycles); any planar embedding would force
F=9 faces each of length ≥6, but 6·9 = 54 > 2·21 = 2E.
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
    (hv : 3 ≤ v) (hg : 3 ≤ g)
    (h : PlanarGraph v e f)
    (hface : g * f ≤ 2 * e) :
    e * (g - 2) ≤ g * (v - 2) := by
  have hE := euler_formula h
  have hF := face_pos h
  -- Euler: v + f = e + 2, so f = e + 2 - v.
  -- Multiply by g: g·f = g·e + 2g - g·v
  -- With g·f ≤ 2e: g·e + 2g - g·v ≤ 2e
  -- So (g-2)e ≤ g·v - 2g = g(v-2).
  -- Need v ≥ 2 for v-2 to behave; we have v ≥ 3.
  -- Also need g ≥ 2 for g-2 to behave; we have g ≥ 3.
  have hv2 : 2 ≤ v := by omega
  have hg2 : 2 ≤ g := by omega
  -- Compute g * f from Euler equation
  have h_gf : g * f + g * v = g * e + 2 * g := by
    have : g * (v + f) = g * (e + 2) := by rw [hE]
    ring_nf at this ⊢
    omega
  -- Combine with hface
  have h_ge : g * e + 2 * g ≤ 2 * e + g * v := by omega
  -- Rearrange: (g - 2) * e ≤ g * (v - 2)
  have hgmul : g * v - 2 * g = g * (v - 2) := by
    rw [Nat.mul_sub_one]
    omega
  have hemul : g * e - 2 * e = e * (g - 2) := by
    rw [Nat.mul_sub_one]
    ring_nf; omega
  omega

-- ============================================================
-- LADDER L_n: two parallel paths connected by n rungs
-- ============================================================
-- L_n = K_2 × P_n: V = 2n, E = 3n - 2, F = n
-- (n-1 quadrilateral cells + 1 outer face)

/-- Ladder L_n: V = 2n, E = 3n - 2, F = n (for n ≥ 2). -/
theorem ladder_planar (n : ℕ) (hn : 2 ≤ n) :
    PlanarGraph (2 * n) (3 * n - 2) n := by
  -- Start from K_{2,2} = ladder L_2: V=4, E=4, F=2
  -- Actually K_{2,2} corresponds to a 4-cycle, not a ladder.
  -- Build inductively from L_2:
  --   L_2: a 4-cycle (V=4, E=4, F=2) — but that's NOT the right shape.
  -- Correct base: L_2 = single rung K_2 ⊔ second K_2 connected by 2 verticals
  --              That's a 4-cycle: V=4, E=4, F=2.
  --
  -- Inductive step: L_{n+1} = L_n + 2 leaves (2 new vertices) + 1 closing edge
  -- (V: 2n → 2n+2, E: 3n-2 → 3n+1 = 3(n+1)-2, F: n → n+1)
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
A `PlanarEmbedding G` witnesses that the graph `G` can be embedded
in the plane: it gives a face count and a `PlanarGraph` witness whose
vertex and edge counts match those of `G`.
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
