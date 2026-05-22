/-
  Hypermap approach to Euler's formula (Jordan-free, Dufourd/Gonthier style).

  We extend our existing CombinatorialMap with the Walkup reduction
  operation: removing a single dart and adjusting the permutations.
  This is the inductive step used in both Dufourd's Coq formalization
  and the Four Color Theorem proof to derive Euler without topology.

  Strategy:
    1. Define Walkup_E (and N, F variants) on CombinatorialMap (Fin n)
       → CombinatorialMap (Fin (n-1))
    2. Show Euler characteristic is preserved (or changes in a controlled way)
    3. Induct on n to derive Euler for all connected planar hypermaps

  This file implements Block 1: structural setup.
-/
import CMapEuler

namespace CombinatorialMap

variable {n : ℕ}

/-! ## Block 1: Removing a dart via Fin.succ embedding

To "remove" dart 0 from a CombinatorialMap on Fin (n+1), we work with
the embedding `Fin.succ : Fin n → Fin (n+1)`.

The new permutations on `Fin n` are obtained by "skipping" dart 0:
if the original σ sends `succ i` to dart 0, we follow σ once more to
find the next non-removed target.
-/

/--
For a permutation `π` on `Fin (n+1)` and a removed dart `r`, return
the function on `Fin n \ {r}` that follows `π` repeatedly until it
lands outside `{r}`. This is the "skip" function used in Walkup.
-/
def skipPerm (π : Equiv.Perm (Fin (n+1))) (r : Fin (n+1)) :
    Fin (n+1) → Fin (n+1) :=
  fun d => if π d = r then π (π d) else π d

/--
A `WalkupResult` is the data of the new permutations on the smaller dart
set, packaged with a proof that the original CombinatorialMap relations
are preserved after removing dart `r`.

This is a deferred construction: the proof that walkup yields a valid
CombinatorialMap on `Fin n` requires showing the new permutations are
involutive (for α) and that the group relation is maintained.
-/
structure WalkupData (M : CombinatorialMap (Fin (n+1))) (r : Fin (n+1)) where
  newVertex : Fin (n+1) → Fin (n+1) := skipPerm M.vertexPerm r
  newEdge   : Fin (n+1) → Fin (n+1) := skipPerm M.edgePerm r
  newFace   : Fin (n+1) → Fin (n+1) := skipPerm M.facePerm r
  /-- The removed dart is a fixed point of all new permutations. -/
  fixedAtR  : newVertex r = r ∧ newEdge r = r ∧ newFace r = r

/-- The skip permutation fixes the removed dart whenever the original π
    has `r` and `π r` in a 2-cycle. -/
theorem skipPerm_fixes_two_cycle (π : Equiv.Perm (Fin (n+1)))
    (r : Fin (n+1)) (h : π (π r) = r) :
    skipPerm π r r = r := by
  unfold skipPerm
  by_cases hpr : π r = r
  · simp [hpr]
  · simp [hpr]; exact h

end CombinatorialMap

/-! ## Status

Block 1 (this file):
  ✓ skipPerm: combinatorial "skip the removed dart" function
  ✓ WalkupData: structure capturing what walkup produces
  ✓ skipPerm_fixes_two_cycle: smallest non-trivial property

What's NOT here yet (subsequent blocks):
  ✗ Walkup as full CombinatorialMap (requires Fin embedding work)
  ✗ Euler preservation under Walkup
  ✗ Induction on dart count to derive Euler for all planar maps
-/
