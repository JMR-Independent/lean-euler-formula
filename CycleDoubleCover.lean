/-
  Cycle Double Cover approach to Euler's formula (Jordan-free).

  Strategy: in a planar graph embedded in the plane, the set of face
  boundaries forms a "cycle double cover": each edge belongs to exactly
  2 face cycles. From this combinatorial fact, Euler's formula follows
  by counting edge-incidences.

  Argument:
    Each face f has some boundary length deg(f) ≥ 3.
    Sum of all face degrees = 2E  (each edge in exactly 2 faces).
    So Σ deg(f) = 2E.
    If all faces are triangles: 3F = 2E.
    Combined with V - E + F = 2 (which we're trying to prove):
    we can derive F directly from V and E given the face structure.

  This file isolates the COMBINATORIAL CORE.
-/
import Mathlib.Tactic

namespace CycleDoubleCover

/--
A **face-degree sequence** for a planar graph: a list of face degrees
such that their sum equals 2E (cycle double cover property).
-/
structure FaceDegrees where
  /-- The number of edges in the graph. -/
  E : ℕ
  /-- The face degrees (one per face, each ≥ 1). -/
  degrees : List ℕ
  /-- Each face has positive degree. -/
  all_pos : ∀ d ∈ degrees, 1 ≤ d
  /-- Cycle double cover: sum of degrees = 2E. -/
  sum_eq_two_E : degrees.sum = 2 * E

namespace FaceDegrees

variable (fd : FaceDegrees)

/-- The face count is the length of the degrees list. -/
def F : ℕ := fd.degrees.length

/-- If every face has degree ≥ 3, then 3F ≤ 2E. -/
theorem three_F_le_two_E
    (h : ∀ d ∈ fd.degrees, 3 ≤ d) :
    3 * fd.F ≤ 2 * fd.E := by
  have hsum : fd.degrees.sum = 2 * fd.E := fd.sum_eq_two_E
  have hge : 3 * fd.degrees.length ≤ fd.degrees.sum := by
    induction fd.degrees with
    | nil => simp
    | cons d ds ih =>
      simp only [List.length_cons, List.sum_cons]
      have hd : 3 ≤ d := h d (List.mem_cons_self d ds)
      have ih' : 3 * ds.length ≤ ds.sum := ih (fun x hx => h x (List.mem_cons_of_mem d hx))
      linarith
  rw [F]; omega

/-- If every face has degree ≥ 4 (bipartite), then 4F ≤ 2E. -/
theorem four_F_le_two_E
    (h : ∀ d ∈ fd.degrees, 4 ≤ d) :
    4 * fd.F ≤ 2 * fd.E := by
  have hsum : fd.degrees.sum = 2 * fd.E := fd.sum_eq_two_E
  have hge : 4 * fd.degrees.length ≤ fd.degrees.sum := by
    induction fd.degrees with
    | nil => simp
    | cons d ds ih =>
      simp only [List.length_cons, List.sum_cons]
      have hd : 4 ≤ d := h d (List.mem_cons_self d ds)
      have ih' : 4 * ds.length ≤ ds.sum := ih (fun x hx => h x (List.mem_cons_of_mem d hx))
      linarith
  rw [F]; omega

end FaceDegrees

/--
**The Cycle Double Cover ⟹ Euler bound theorem**:
A planar graph with face-degree sequence (CDC) satisfying min degree ≥ 3
has E ≤ 3V - 6, provided V + F = E + 2 holds.

This isolates the COMBINATORIAL content of Euler's bound: given the
double-cover property (sum of face degrees = 2E) and Euler V+F = E+2,
the edge bound E ≤ 3V - 6 follows by pure arithmetic.
-/
theorem cdc_edge_bound (V F E : ℕ) (fd : FaceDegrees)
    (hE : fd.E = E) (hF : fd.F = F)
    (hmin : ∀ d ∈ fd.degrees, 3 ≤ d)
    (hEuler : V + F = E + 2)
    (hV : 3 ≤ V) :
    E ≤ 3 * V - 6 := by
  have h3F := fd.three_F_le_two_E hmin
  rw [hF, hE] at h3F
  omega

end CycleDoubleCover
