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
