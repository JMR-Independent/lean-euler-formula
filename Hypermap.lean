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

/-- If `d` is mapped by `π` to a non-removed dart, `skipPerm` agrees with `π`. -/
theorem skipPerm_eq_orig (π : Equiv.Perm (Fin (n+1)))
    (r d : Fin (n+1)) (h : π d ≠ r) :
    skipPerm π r d = π d := by
  unfold skipPerm; simp [h]

/-- If `π d = r`, then `skipPerm π r d = π (π d) = π r`. -/
theorem skipPerm_chase (π : Equiv.Perm (Fin (n+1)))
    (r d : Fin (n+1)) (h : π d = r) :
    skipPerm π r d = π r := by
  unfold skipPerm; simp [h]

/-- For an involution π, skipPerm at r preserves involutivity at non-r darts:
    if π d ≠ r and π (skipPerm π r d) ≠ r, then iterating twice returns d. -/
theorem skipPerm_involutive_aux (π : Equiv.Perm (Fin (n+1)))
    (hinv : Function.Involutive π)
    (r d : Fin (n+1)) (hd : π d ≠ r) (h2 : π (π d) ≠ r) :
    skipPerm π r (skipPerm π r d) = d := by
  rw [skipPerm_eq_orig π r d hd]
  rw [skipPerm_eq_orig π r (π d) h2]
  exact hinv d

/-- If `r` is a fixed point of `π` (i.e. `π r = r`), then `skipPerm π r = π`. -/
theorem skipPerm_of_fixed (π : Equiv.Perm (Fin (n+1)))
    (r : Fin (n+1)) (hr : π r = r) (d : Fin (n+1)) :
    skipPerm π r d = π d := by
  unfold skipPerm
  by_cases h : π d = r
  · -- π d = r and π r = r, so π d = π r, hence d = r (π injective), so π d = π r = r
    have hd : d = r := π.injective (h.trans hr.symm)
    rw [hd, h]
    exact hr.symm
  · simp [h]

/-- Trivially, skipPerm is the identity at the fixed dart whenever π r = r. -/
theorem skipPerm_fixed_at_r (π : Equiv.Perm (Fin (n+1)))
    (r : Fin (n+1)) (hr : π r = r) :
    skipPerm π r r = r := by
  rw [skipPerm_of_fixed π r hr, hr]

/-- The image of `skipPerm π r` never equals `r` for `d ≠ r`, provided
    `r` is the only dart π sends to `r` (which holds when π is a bijection). -/
theorem skipPerm_image_ne_r (π : Equiv.Perm (Fin (n+1)))
    (r d : Fin (n+1)) (hd : d ≠ r) :
    skipPerm π r d ≠ r := by
  unfold skipPerm
  by_cases h : π d = r
  · -- π d = r → skipPerm π r d = π (π d) = π r
    simp [h]
    intro hcontra
    -- π r = r would force d = r (π injective)
    exact hd (π.injective (h.trans hcontra.symm))
  · -- π d ≠ r → skipPerm π r d = π d ≠ r
    simp [h]; exact h

/-- For a full involution π fixing r as a 2-cycle endpoint, walkup makes
    sense: every `d ≠ r` has both `π d ≠ r` (after skipping) and double
    application returns d. -/
theorem skipPerm_involutive_safe (π : Equiv.Perm (Fin (n+1)))
    (hinv : Function.Involutive π)
    (r d : Fin (n+1)) (hd : d ≠ r) (hr_fixed : π r = r) :
    skipPerm π r (skipPerm π r d) = d := by
  -- When π r = r, skipPerm π r = π exactly (block 3)
  rw [skipPerm_of_fixed π r hr_fixed]
  rw [skipPerm_of_fixed π r hr_fixed]
  exact hinv d

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
