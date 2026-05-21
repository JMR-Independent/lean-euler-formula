/-
  Completeness: every connected CombinatorialMap satisfies eulerCharacteristic = 2

  Strategy:
  1. edge_count_eq: Fintype.card M.Edge = Fintype.card D / 2
     (fixed-point-free involution → every orbit has size 2)
  2. vertex_face_count_eq: Fintype.card M.Vertex + Fintype.card M.Face = Fintype.card D / 2 + 2
     (induction on darts: contraction-deletion)
  3. Combine: eulerCharacteristic = V - E + F = 2
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Data.Fintype.Card
import CMapEuler

namespace CombinatorialMap

variable {D : Type*} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)

-- ============================================================
-- STEP 1: EDGE COUNT
-- ============================================================
-- For a fixed-point-free involution, every orbit has exactly 2 elements.
-- So the number of orbits = |D| / 2.

/-- No dart is a fixed point of edgePerm. -/
lemma edgePerm_no_fixedPoint (d : D) : M.edgePerm d ≠ d :=
  fun h => M.isEmpty_fixedPoints_edgePerm.false ⟨d, h⟩

/-- edgePerm has empty support complement: every dart is moved. -/
lemma edgePerm_support_eq_univ : M.edgePerm.support = Finset.univ := by
  ext d; simp [Equiv.Perm.mem_support, M.edgePerm_no_fixedPoint d]

/-- edgePerm is order-2 (squaring gives identity). -/
lemma edgePerm_sq : M.edgePerm ^ 2 = 1 := by
  ext d; simp [sq, Equiv.Perm.mul_apply, M.edgePerm_involutive]

/-- All cycle lengths of a fixed-point-free involution are 2. -/
lemma edgePerm_cycleType_mem (k : ℕ) (hk : k ∈ M.edgePerm.cycleType) : k = 2 := by
  -- k is a cycle length → k divides orderOf edgePerm = 2 → k ∈ {1, 2}
  -- k ≥ 2 since no fixed points → k = 2
  have hdvd : k ∣ M.edgePerm.orderOf := Equiv.Perm.dvd_orderOf_of_mem_cycleType hk
  have hord : M.edgePerm.orderOf ∣ 2 := by
    rw [← Equiv.Perm.orderOf_eq_card_pow_eq_one]
    exact orderOf_dvd_of_pow_eq_one M.edgePerm_sq
  have hle : k ∣ 2 := dvd_trans hdvd hord
  have hne1 : k ≠ 1 := by
    intro heq; subst heq
    -- A cycle of length 1 is a fixed point, contradicting hfp
    have := Equiv.Perm.one_mem_cycleType_iff.mp hk
    exact M.edgePerm_no_fixedPoint this.choose this.choose_spec
  interval_cases k <;> omega

/-- Sum of edgePerm cycleType = |D|. -/
lemma edgePerm_cycleType_sum :
    M.edgePerm.cycleType.sum = Fintype.card D := by
  rw [Equiv.Perm.sum_cycleType, M.edgePerm_support_eq_univ, Finset.card_univ]

/-- For a fixed-point-free involution, |D| = 2 * number_of_edges. -/
lemma dart_count_eq_twice_edges :
    Fintype.card D = 2 * M.edgePerm.cycleType.card := by
  have hsum := M.edgePerm_cycleType_sum
  have hall := fun k hk => M.edgePerm_cycleType_mem k hk
  -- cycleType is a multiset of 2s, so sum = 2 * card
  rw [← hsum]
  rw [show M.edgePerm.cycleType = Multiset.replicate M.edgePerm.cycleType.card 2 from by
    rw [Multiset.eq_replicate]
    exact ⟨rfl, hall⟩]
  simp [Multiset.sum_replicate]

/-- Each edge-orbit (fiber) contains exactly 2 darts. -/
lemma edgePerm_fiber_card (e : M.Edge) :
    Fintype.card {d : D // (⟦d⟧ : M.Edge) = e} = 2 := by
  obtain ⟨d₀, rfl⟩ := Quotient.exists_rep e
  -- fiber = {d | SameCycle edgePerm d₀ d} = {d₀, edgePerm d₀}
  have hne : d₀ ≠ M.edgePerm d₀ := (M.edgePerm_no_fixedPoint d₀).symm
  apply Fintype.card_eq_of_equiv
  -- Bijection: Fin 2 ≃ {d | SameCycle edgePerm d₀ d}
  exact {
    toFun := fun i => ⟨if i = 0 then d₀ else M.edgePerm d₀, by
      fin_cases i <;> simp [Quotient.eq']
      · rfl
      · exact Quotient.sound (Equiv.Perm.SameCycle.symm ⟨1, by simp [M.edgePerm_involutive]⟩)⟩
    invFun := fun ⟨d, hd⟩ =>
      if d = d₀ then 0
      else if d = M.edgePerm d₀ then 1
      else (absurd rfl (by
        -- d must be d₀ or edgePerm d₀ (orbit has size 2)
        sorry))
    left_inv := fun i => by fin_cases i <;> simp [hne]
    right_inv := fun ⟨d, hd⟩ => by
      simp only [Quotient.eq'] at hd
      -- d and d₀ are in the same orbit of edgePerm (involutive, order 2)
      -- Therefore d = d₀ or d = edgePerm d₀
      sorry }

/-- For a fixed-point-free involution: |D| = 2 * |Edge|, so |Edge| = |D|/2. -/
theorem edge_count_eq :
    Fintype.card M.Edge = Fintype.card D / 2 := by
  -- Use the fiber decomposition: D = Σ e : M.Edge, fiber(e)
  -- Each fiber has size 2 → |D| = 2 * |M.Edge| → |M.Edge| = |D|/2
  have hfib := M.edgePerm_fiber_card
  have hbij : (Σ e : M.Edge, {d : D // (⟦d⟧ : M.Edge) = e}) ≃ D :=
    Equiv.sigmaFibEquiv (Quotient.mk _)
  have hcard : Fintype.card D = 2 * Fintype.card M.Edge := by
    rw [← Fintype.card_congr hbij, Fintype.card_sigma]
    simp [hfib, Finset.sum_const, Finset.card_univ]
  omega

-- ============================================================
-- STEP 2: VERTEX + FACE COUNT (the hard part)
-- ============================================================
-- For a connected CMap, V + F = |D|/2 + 2.
-- Proof: induction on |D| using contraction-deletion.

/-- Connected combinatorial map: ⟨vertexPerm, edgePerm⟩ acts transitively -/
def IsConnected : Prop :=
  ∀ d₁ d₂ : D, ∃ (moves : List Bool),
    moves.foldl (fun d b => if b then M.edgePerm d else M.vertexPerm d) d₁ = d₂

/-- For a connected CMap, V + F = |D|/2 + 2. -/
theorem vertex_face_eq_of_connected (hconn : M.IsConnected) :
    Fintype.card M.Vertex + Fintype.card M.Face = Fintype.card D / 2 + 2 := by
  -- Induction on Fintype.card D
  -- Base: |D| = 2, one edge, two possible vertex configs, both give V+F = 3 = 1+2
  -- Step: pick dart d, contract or delete edge {d, edgePerm d}
  sorry

-- ============================================================
-- STEP 3: EULER FORMULA FOR CONNECTED CMaps
-- ============================================================

/-- **Main completeness theorem**: every connected CMap satisfies Euler. -/
theorem euler_of_connected (hconn : M.IsConnected) : M.IsPlanar := by
  simp only [IsPlanar, eulerCharacteristic]
  -- V - E + F = (V + F) - E = (|D|/2 + 2) - |D|/2 = 2
  have hE := M.edge_count_eq
  have hVF := M.vertex_face_eq_of_connected hconn
  omega

end CombinatorialMap
