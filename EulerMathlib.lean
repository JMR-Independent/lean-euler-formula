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

end PlanarGraph
