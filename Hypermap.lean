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

/-! ## Block 5: Walkup — full 2-dart edge collapse

Given a CombinatorialMap `M` on `Fin (n+2)` (at least 2 darts) and a
dart `r`, removing the edge `{r, edgePerm r}` reduces to a map on `Fin n`.

We define this via embedding into the larger type and extending by identity
on the removed darts. This avoids re-indexing surgery and keeps the proofs
algebraic.

The "extended" Walkup is a CMap on `Fin (n+2)` where both `r` and `edge r`
become fixed points of all three permutations (effectively isolated).
The orbit counts change by:
  - vertices: V → V - 1 if r and edge r were in different vertices,
              V → V       if they were in the same vertex
  - edges:    E → E - 1 (the edge {r, edge r} disappears)
  - faces:    F → F - 1 if r and edge r were in different faces (deletion),
              F → F       if same face (contraction creates a new face)
-/

namespace CombinatorialMap

/-- The conjugate permutation collapsing the edge `{r, π r}`: agrees with
`π` everywhere except sends r → r and (π r) → (π r). -/
def collapseEdge (π : Equiv.Perm (Fin (n+1))) (r : Fin (n+1)) :
    Fin (n+1) → Fin (n+1) :=
  fun d => if d = r ∨ d = π r then d else π d

theorem collapseEdge_fixes_r (π : Equiv.Perm (Fin (n+1))) (r : Fin (n+1)) :
    collapseEdge π r r = r := by
  unfold collapseEdge; simp

theorem collapseEdge_fixes_pr (π : Equiv.Perm (Fin (n+1))) (r : Fin (n+1)) :
    collapseEdge π r (π r) = π r := by
  unfold collapseEdge; simp

theorem collapseEdge_eq_orig (π : Equiv.Perm (Fin (n+1))) (r d : Fin (n+1))
    (hd1 : d ≠ r) (hd2 : d ≠ π r) :
    collapseEdge π r d = π d := by
  unfold collapseEdge
  simp [hd1, hd2]

/-- If π is involutive and d is neither r nor π r, then π d is also
neither r nor π r (by injectivity). -/
theorem collapseEdge_image_safe (π : Equiv.Perm (Fin (n+1)))
    (hinv : Function.Involutive π) (r d : Fin (n+1))
    (hd1 : d ≠ r) (hd2 : d ≠ π r) :
    π d ≠ r ∧ π d ≠ π r := by
  refine ⟨?_, ?_⟩
  · -- π d = r would mean d = π r (apply π to both sides, use involutive)
    intro h
    apply hd2
    have := congrArg π h
    rw [hinv d] at this
    exact this
  · -- π d = π r would mean d = r (π injective)
    intro h
    exact hd1 (π.injective h)

/-- collapseEdge preserves involutivity at darts disjoint from {r, π r}. -/
theorem collapseEdge_involutive (π : Equiv.Perm (Fin (n+1)))
    (hinv : Function.Involutive π) (r d : Fin (n+1)) :
    collapseEdge π r (collapseEdge π r d) = d := by
  by_cases h1 : d = r
  · subst h1
    rw [collapseEdge_fixes_r, collapseEdge_fixes_r]
  by_cases h2 : d = π r
  · subst h2
    rw [collapseEdge_fixes_pr, collapseEdge_fixes_pr]
  -- Generic case: d ≠ r and d ≠ π r
  rw [collapseEdge_eq_orig π r d h1 h2]
  obtain ⟨hne1, hne2⟩ := collapseEdge_image_safe π hinv r d h1 h2
  rw [collapseEdge_eq_orig π r (π d) hne1 hne2]
  exact hinv d

/-- collapseEdge of an involution is bijective (since it's involutive). -/
theorem collapseEdge_bijective (π : Equiv.Perm (Fin (n+1)))
    (hinv : Function.Involutive π) (r : Fin (n+1)) :
    Function.Bijective (collapseEdge π r) :=
  Function.Involutive.bijective (collapseEdge_involutive π hinv r)

/-- The collapseEdge as an Equiv.Perm (when applied to an involution). -/
noncomputable def collapseEdgePerm (π : Equiv.Perm (Fin (n+1)))
    (hinv : Function.Involutive π) (r : Fin (n+1)) :
    Equiv.Perm (Fin (n+1)) :=
  Equiv.ofBijective (collapseEdge π r) (collapseEdge_bijective π hinv r)

/-- Coercion: collapseEdgePerm acts like collapseEdge. -/
@[simp] theorem collapseEdgePerm_apply (π : Equiv.Perm (Fin (n+1)))
    (hinv : Function.Involutive π) (r d : Fin (n+1)) :
    collapseEdgePerm π hinv r d = collapseEdge π r d := rfl

/-! ## Block 8: Walkup — making both r and (edge r) fixed everywhere

The Walkup operation produces a new CombinatorialMap on Fin (n+1)
where the dart pair {r, edge r} becomes "isolated":
  - new edgePerm = collapseEdge of old edgePerm
  - new vertexPerm = also collapses the same {r, edge r} to fixed points
  - new facePerm = same

This requires the new permutations to satisfy:
  new_face * new_edge * new_vertex = 1

We approach it via a SIMPLIFIED definition: the Walkup just turns
{r, edge r} into fixed points in all three perms. The group relation
needs to be re-verified.
-/

/-- Walkup permutation: collapseEdge using the SAME edge `r, edgePerm r`
but applied to an arbitrary permutation `π`. We collapse w.r.t. the
edge defined by M.edgePerm at dart r. -/
def walkupAt (π : Equiv.Perm (Fin (n+1))) (r₁ r₂ : Fin (n+1)) :
    Fin (n+1) → Fin (n+1) :=
  fun d => if d = r₁ ∨ d = r₂ then d else π d

theorem walkupAt_fixes_r₁ (π : Equiv.Perm (Fin (n+1))) (r₁ r₂ : Fin (n+1)) :
    walkupAt π r₁ r₂ r₁ = r₁ := by
  unfold walkupAt; simp

theorem walkupAt_fixes_r₂ (π : Equiv.Perm (Fin (n+1))) (r₁ r₂ : Fin (n+1)) :
    walkupAt π r₁ r₂ r₂ = r₂ := by
  unfold walkupAt; simp

theorem walkupAt_eq_orig (π : Equiv.Perm (Fin (n+1))) (r₁ r₂ d : Fin (n+1))
    (h₁ : d ≠ r₁) (h₂ : d ≠ r₂) :
    walkupAt π r₁ r₂ d = π d := by
  unfold walkupAt; simp [h₁, h₂]

/-! ## Block 9: The walkup-image-safety lemma

If π is a bijection that maps {r₁, r₂} to itself (i.e., r₁ ↦ r₂ and r₂ ↦ r₁,
or both fixed), then π preserves the complement of {r₁, r₂}.

In our setting, we need the original permutations to FIX both r₁ and r₂
for the walkup to be a clean modification. This is a strong assumption,
captured here as `MapsFixedPair`.
-/

/-- `π` fixes the pair `{r₁, r₂}` pointwise: both are fixed points of `π`. -/
def MapsFixedPair (π : Equiv.Perm (Fin (n+1))) (r₁ r₂ : Fin (n+1)) : Prop :=
  π r₁ = r₁ ∧ π r₂ = r₂

/-- If π fixes both r₁ and r₂, then walkupAt π r₁ r₂ = π everywhere. -/
theorem walkupAt_of_fixed (π : Equiv.Perm (Fin (n+1))) (r₁ r₂ : Fin (n+1))
    (h : MapsFixedPair π r₁ r₂) :
    ∀ d, walkupAt π r₁ r₂ d = π d := by
  intro d
  by_cases h₁ : d = r₁
  · subst h₁; rw [walkupAt_fixes_r₁]; exact h.1.symm
  by_cases h₂ : d = r₂
  · subst h₂; rw [walkupAt_fixes_r₂]; exact h.2.symm
  exact walkupAt_eq_orig π r₁ r₂ d h₁ h₂

/-- The image of walkupAt π r₁ r₂ stays away from {r₁, r₂} for d ≠ r₁, r₂,
provided π also fixes {r₁, r₂} pointwise. -/
theorem walkupAt_image_safe (π : Equiv.Perm (Fin (n+1))) (r₁ r₂ d : Fin (n+1))
    (h : MapsFixedPair π r₁ r₂) (h₁ : d ≠ r₁) (h₂ : d ≠ r₂) :
    walkupAt π r₁ r₂ d ≠ r₁ ∧ walkupAt π r₁ r₂ d ≠ r₂ := by
  rw [walkupAt_eq_orig π r₁ r₂ d h₁ h₂]
  refine ⟨?_, ?_⟩
  · intro hcontra; exact h₁ (π.injective (hcontra.trans h.1.symm))
  · intro hcontra; exact h₂ (π.injective (hcontra.trans h.2.symm))

/-! ## Block 10: composition preservation

Key theorem: if face, edge, vertex all fix {r₁, r₂} and their composition
is the identity, then their walkups also compose to the identity.
-/

/-- Composition of walkupAt preserves the identity group relation. -/
theorem walkupAt_composition
    (f e v : Equiv.Perm (Fin (n+1)))
    (r₁ r₂ : Fin (n+1))
    (hf : MapsFixedPair f r₁ r₂)
    (he : MapsFixedPair e r₁ r₂)
    (hv : MapsFixedPair v r₁ r₂)
    (hcomp : ∀ d, f (e (v d)) = d)
    (d : Fin (n+1)) :
    walkupAt f r₁ r₂ (walkupAt e r₁ r₂ (walkupAt v r₁ r₂ d)) = d := by
  -- Since all three perms fix r₁ and r₂, walkupAt = original perm pointwise.
  rw [walkupAt_of_fixed v r₁ r₂ hv d]
  rw [walkupAt_of_fixed e r₁ r₂ he (v d)]
  rw [walkupAt_of_fixed f r₁ r₂ hf (e (v d))]
  exact hcomp d

/-! ## Block 11: degeneracy — walkup at already-fixed pair is identity

The honest characterization of what Block 10 says:
when all three permutations already fix the pair, walking up does nothing.
The map is unchanged. This is consistent because in a true CMap,
edgePerm has NO fixed points — so no dart of edgePerm is "already fixed".

Therefore: the framework of MapsFixedPair-style walkup is too weak to
reduce a real CombinatorialMap. We need a different approach:
ACTUAL walkup that changes edgePerm via collapseEdge, NOT one that
requires fixing to already hold.

This is documented honestly: Block 10's composition theorem holds
trivially because nothing changed. For the REAL Dufourd-style walkup,
we need to define collapseEdge for σ and φ in a way that depends on
the edge r ↔ edgePerm r structure, not on σ already fixing them.
-/

/-- Walkup at a non-trivial dart: defined ONLY when the chosen r is NOT
a fixed point of M.edgePerm. This is the Dufourd Walkup. -/
def DufourdWalkupParameter (M : CombinatorialMap (Fin (n+1))) : Type :=
  { r : Fin (n+1) // M.edgePerm r ≠ r }

theorem dufourdWalkupParameter_exists (M : CombinatorialMap (Fin (n+1))) :
    Nonempty (M.DufourdWalkupParameter) := by
  refine ⟨⟨0, ?_⟩⟩
  intro h
  exact M.isEmpty_fixedPoints_edgePerm.false ⟨0, h⟩

end CombinatorialMap

/-! ## Block 12: Concrete instances satisfy vanStaudt_arith partition

For each concrete CMap, verify the Van Staudt partition hypothesis
(V-1) + (F-1) = E. Combined with `vanStaudt_arith`, this gives a
Jordan-free derivation of Euler for each one.
-/

theorem singleEdgeMap_vanStaudt :
    (Fintype.card singleEdgeMap.Vertex - 1) +
    (Fintype.card singleEdgeMap.Face - 1) =
    Fintype.card singleEdgeMap.Edge := by
  native_decide

theorem triangleMap_vanStaudt :
    (Fintype.card triangleMap.Vertex - 1) +
    (Fintype.card triangleMap.Face - 1) =
    Fintype.card triangleMap.Edge := by
  native_decide

theorem k4Map_vanStaudt :
    (Fintype.card k4Map.Vertex - 1) +
    (Fintype.card k4Map.Face - 1) =
    Fintype.card k4Map.Edge := by
  native_decide

theorem cubeMap_vanStaudt :
    (Fintype.card cubeMap.Vertex - 1) +
    (Fintype.card cubeMap.Face - 1) =
    Fintype.card cubeMap.Edge := by
  native_decide

theorem octahedronMap_vanStaudt :
    (Fintype.card octahedronMap.Vertex - 1) +
    (Fintype.card octahedronMap.Face - 1) =
    Fintype.card octahedronMap.Edge := by
  native_decide

/-- The torus map FAILS the Van Staudt partition: it has no valid
spanning tree decomposition because it's not planar. -/
theorem torusCMap_fails_vanStaudt :
    (Fintype.card torusCMap.Vertex - 1) +
    (Fintype.card torusCMap.Face - 1) ≠
    Fintype.card torusCMap.Edge := by
  native_decide

/-! ## Block 13: Jordan-free Euler for concrete CMaps via vanStaudt_arith

Each concrete planar CMap satisfies V + F = E + 2 derived using ONLY:
- The Van Staudt partition (verified by native_decide)
- The arithmetic core vanStaudt_arith (proved in EulerMathlib by omega)

NO Jordan curve theorem, NO PlanarGraph induction, NO topology.
Pure arithmetic + verified partition.
-/

theorem singleEdgeMap_euler_jordan_free :
    Fintype.card singleEdgeMap.Vertex + Fintype.card singleEdgeMap.Face =
    Fintype.card singleEdgeMap.Edge + 2 :=
  PlanarGraph.vanStaudt_arith _ _ _
    (by native_decide) (by native_decide) singleEdgeMap_vanStaudt

theorem triangleMap_euler_jordan_free :
    Fintype.card triangleMap.Vertex + Fintype.card triangleMap.Face =
    Fintype.card triangleMap.Edge + 2 :=
  PlanarGraph.vanStaudt_arith _ _ _
    (by native_decide) (by native_decide) triangleMap_vanStaudt

theorem k4Map_euler_jordan_free :
    Fintype.card k4Map.Vertex + Fintype.card k4Map.Face =
    Fintype.card k4Map.Edge + 2 :=
  PlanarGraph.vanStaudt_arith _ _ _
    (by native_decide) (by native_decide) k4Map_vanStaudt

theorem cubeMap_euler_jordan_free :
    Fintype.card cubeMap.Vertex + Fintype.card cubeMap.Face =
    Fintype.card cubeMap.Edge + 2 :=
  PlanarGraph.vanStaudt_arith _ _ _
    (by native_decide) (by native_decide) cubeMap_vanStaudt

theorem octahedronMap_euler_jordan_free :
    Fintype.card octahedronMap.Vertex + Fintype.card octahedronMap.Face =
    Fintype.card octahedronMap.Edge + 2 :=
  PlanarGraph.vanStaudt_arith _ _ _
    (by native_decide) (by native_decide) octahedronMap_vanStaudt

/-! ## Block 14: A general Jordan-free Euler theorem for CMaps

Package the Jordan-free derivation as a reusable theorem on any CMap
with a Van Staudt partition.
-/

/--
**Jordan-free Euler theorem for CombinatorialMaps**:
Any CombinatorialMap M with V ≥ 1, F ≥ 1, and a valid Van Staudt
partition (V-1)+(F-1) = E satisfies V + F = E + 2.

No Jordan curve theorem used. The substantive content (constructing
the spanning trees) is delegated to the partition hypothesis.
-/
theorem CombinatorialMap.euler_via_vanStaudt
    {D : Type*} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)
    (hV : 1 ≤ Fintype.card M.Vertex)
    (hF : 1 ≤ Fintype.card M.Face)
    (hPart : (Fintype.card M.Vertex - 1) + (Fintype.card M.Face - 1) =
             Fintype.card M.Edge) :
    Fintype.card M.Vertex + Fintype.card M.Face =
    Fintype.card M.Edge + 2 :=
  PlanarGraph.vanStaudt_arith _ _ _ hV hF hPart

/--
Signed (integer) form of the Jordan-free Euler theorem for CMaps.
-/
theorem CombinatorialMap.eulerChar_via_vanStaudt
    {D : Type*} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)
    (hV : 1 ≤ Fintype.card M.Vertex)
    (hF : 1 ≤ Fintype.card M.Face)
    (hPart : (Fintype.card M.Vertex - 1) + (Fintype.card M.Face - 1) =
             Fintype.card M.Edge) :
    M.eulerCharacteristic = 2 := by
  simp only [CombinatorialMap.eulerCharacteristic]
  have := M.euler_via_vanStaudt hV hF hPart
  omega

/-! ## Block 15: Concrete walkup verification on singleEdgeMap

Apply collapseEdge to the actual edgePerm of singleEdgeMap and verify
the result fixes both darts. This is the smallest concrete test of
our Walkup infrastructure.
-/

namespace SingleEdgeWalkupTest

/-- Apply collapseEdge to singleEdgeMap's edgePerm at dart 0. -/
def collapsedEdge : Fin 2 → Fin 2 :=
  CombinatorialMap.collapseEdge singleEdgeMap.edgePerm ⟨0, by decide⟩

/-- After collapse, dart 0 is fixed. -/
theorem collapsed_fixes_0 : collapsedEdge ⟨0, by decide⟩ = ⟨0, by decide⟩ := by
  unfold collapsedEdge
  exact CombinatorialMap.collapseEdge_fixes_r _ _

/-- After collapse, dart 1 (the edge partner) is also fixed. -/
theorem collapsed_fixes_1 : collapsedEdge ⟨1, by decide⟩ = ⟨1, by decide⟩ := by
  unfold collapsedEdge
  -- We need to show: collapseEdge edgePerm 0 (edgePerm 0) = edgePerm 0
  -- edgePerm of singleEdgeMap is swap, so edgePerm 0 = 1
  have h_eq : singleEdgeMap.edgePerm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by
    native_decide
  rw [← h_eq]
  exact CombinatorialMap.collapseEdge_fixes_pr _ _

/-- After collapse, the result is the identity (since both darts are fixed). -/
theorem collapsed_is_identity : ∀ d, collapsedEdge d = d := by
  intro d
  fin_cases d
  · exact collapsed_fixes_0
  · exact collapsed_fixes_1

end SingleEdgeWalkupTest

/-! ## Block 16: Walkup test on triangleMap

Collapse the first edge {0,1} of triangleMap and verify both darts
become fixed in the resulting edge permutation. The other edges
{2,3} and {4,5} remain untouched.
-/

namespace TriangleWalkupTest

def collapsedEdge : Fin 6 → Fin 6 :=
  CombinatorialMap.collapseEdge triangleMap.edgePerm ⟨0, by decide⟩

theorem collapsed_fixes_0 : collapsedEdge ⟨0, by decide⟩ = ⟨0, by decide⟩ := by
  unfold collapsedEdge
  exact CombinatorialMap.collapseEdge_fixes_r _ _

theorem collapsed_fixes_1 : collapsedEdge ⟨1, by decide⟩ = ⟨1, by decide⟩ := by
  unfold collapsedEdge
  have h_eq : triangleMap.edgePerm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by native_decide
  rw [← h_eq]
  exact CombinatorialMap.collapseEdge_fixes_pr _ _

/-- Darts 2 and 3 (the other edge) are untouched by the collapse. -/
theorem collapsed_preserves_2 :
    collapsedEdge ⟨2, by decide⟩ = triangleMap.edgePerm ⟨2, by decide⟩ := by
  unfold collapsedEdge
  apply CombinatorialMap.collapseEdge_eq_orig
  · decide
  · -- 2 ≠ edgePerm 0 = 1
    have h_eq : triangleMap.edgePerm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by native_decide
    rw [h_eq]; decide

theorem collapsed_preserves_3 :
    collapsedEdge ⟨3, by decide⟩ = triangleMap.edgePerm ⟨3, by decide⟩ := by
  unfold collapsedEdge
  apply CombinatorialMap.collapseEdge_eq_orig
  · decide
  · have h_eq : triangleMap.edgePerm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by native_decide
    rw [h_eq]; decide

end TriangleWalkupTest



/-! ## Status

Block 1: ✓ skipPerm + WalkupData
Block 2: ✓ skipPerm properties
Block 3: ✓ skipPerm at fixed points
Block 4: ✓ image bounds + safe involutivity
Block 5: ✓ collapseEdge: makes r and (edge r) fixed points

This is the FOUNDATION for the real Walkup: collapseEdge applied to all
three permutations gives a "smaller in spirit" CMap (two isolated darts
that don't affect orbit counts of the rest).

The induction will then proceed: keep applying collapseEdge until all
darts are isolated, count what we did, derive Euler.

Remaining: proving collapseEdge is involutive when restricted properly,
preserving the group relation, and counting orbit changes.
-/
