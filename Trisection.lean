/-
  Impossibility of doubling the cube (Wiedijk #8).

  We prove the algebraic core of the impossibility theorem:
  in any field extension F/ℚ with [F:ℚ] = 2^k, no element cubes to 2.

  Equivalently: ∛2 is not constructible by compass and straightedge,
  since constructible numbers lie in towers of degree-2 extensions of ℚ,
  giving [F:ℚ] = 2^k for some k. Since [ℚ(∛2):ℚ] = 3 is odd, ∛2 ∉ F.

  Proof outline:
    1. X³ - 2 is irreducible over ℤ by Eisenstein's criterion at p = 2.
    2. By Gauss's lemma, X³ - 2 is irreducible over ℚ.
    3. dim_ℚ AdjoinRoot(X³ - 2) = 3 (from PowerBasis).
    4. If α³ = 2 in F/ℚ, then minpoly ℚ α = X³ - 2, so 3 ∣ [F:ℚ].
    5. 3 ∣ 2^k implies 3 ∣ 2 (prime), contradiction.
-/
import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

open Polynomial IntermediateField

-- ============================================================
-- STEP 1: X³ - 2 IS IRREDUCIBLE OVER ℤ (Eisenstein at p = 2)
-- ============================================================

private noncomputable def cubePoly : ℤ[X] := X ^ 3 - C 2

private lemma cubePoly_monic : cubePoly.Monic :=
  monic_X_pow_sub_C 2 (by norm_num)

/-- X³ - 2 over ℤ satisfies Eisenstein's criterion at the ideal (2). -/
private lemma cubePoly_isEisensteinAt :
    cubePoly.IsEisensteinAt (Ideal.span {(2 : ℤ)}) := by
  apply cubePoly_monic.isEisensteinAt_of_mem_of_notMem
  · -- (2) ≠ ⊤ in ℤ (since 1 ∉ (2))
    rw [Ideal.ne_top_iff_one, Ideal.mem_span_singleton]
    norm_num
  · -- all coefficients below the leading one lie in (2)
    intro n hn
    simp only [cubePoly, natDegree_X_pow_sub_C] at hn
    interval_cases n <;>
      simp [cubePoly, coeff_sub, coeff_X_pow, coeff_C, Ideal.mem_span_singleton]
  · -- constant coefficient -2 is not in (2)² = (4)
    have hc : cubePoly.coeff 0 = -2 := by
      simp [cubePoly, coeff_sub, coeff_X_pow, coeff_C]
    have h4 : (Ideal.span {(2 : ℤ)}) ^ 2 = Ideal.span {(4 : ℤ)} := by
      rw [Ideal.span_singleton_pow]; norm_num
    rw [hc, h4, Ideal.mem_span_singleton]
    norm_num

/-- X³ - 2 is irreducible over ℤ. -/
private lemma cubePoly_irreducible_int : Irreducible cubePoly :=
  cubePoly_isEisensteinAt.irreducible
    ((Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr Int.prime_two)
    cubePoly_monic.isPrimitive
    (by norm_num [cubePoly, natDegree_X_pow_sub_C])

-- ============================================================
-- STEP 2: X³ - 2 IS IRREDUCIBLE OVER ℚ (Gauss's lemma)
-- ============================================================

/-- The polynomial X³ - 2 is irreducible over ℚ. -/
theorem X_cube_sub_two_irreducible : Irreducible (X ^ 3 - C (2 : ℚ)) := by
  have key : Irreducible (cubePoly.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      cubePoly_monic.isPrimitive).mp cubePoly_irreducible_int
  have hmap : cubePoly.map (Int.castRingHom ℚ) = X ^ 3 - C (2 : ℚ) := by
    simp only [cubePoly, map_sub, map_pow, map_X, map_C, Int.cast_ofNat]
  rwa [hmap] at key

-- ============================================================
-- STEP 3: dim_ℚ AdjoinRoot(X³ - 2) = 3
-- ============================================================

/-- The AdjoinRoot field of X³ - 2 has dimension 3 over ℚ. -/
theorem finrank_adjoinRoot_cube :
    Module.finrank ℚ (AdjoinRoot (X ^ 3 - C (2 : ℚ))) = 3 := by
  have hne : (X ^ 3 - C (2 : ℚ)) ≠ 0 := X_cube_sub_two_irreducible.ne_zero
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hne),
      AdjoinRoot.powerBasis_dim hne, natDegree_X_pow_sub_C]

-- ============================================================
-- STEP 4: DOUBLING THE CUBE IS IMPOSSIBLE
-- ============================================================

/-- **Doubling the cube is impossible** (Wiedijk #8).

In any field extension F/ℚ with [F:ℚ] = 2^k, no element cubes to 2.

This formalizes the classical result: the cube root of 2 is not constructible
by compass and straightedge. Constructible numbers lie in a tower of degree-2
extensions over ℚ, giving [F:ℚ] = 2^k. Since [ℚ(∛2):ℚ] = 3 is odd, ∛2
is not in any such tower. -/
theorem cube_doubling_impossible (k : ℕ) {F : Type*} [Field F] [Algebra ℚ F]
    [FiniteDimensional ℚ F] (hk : Module.finrank ℚ F = 2 ^ k)
    (α : F) : α ^ 3 ≠ algebraMap ℚ F 2 := by
  intro hα
  -- α is integral over ℚ (all elements of a finite extension are)
  have hint : IsIntegral ℚ α := IsIntegral.of_finite ℚ α
  -- α is a root of X³ - 2
  have heval : aeval α (X ^ 3 - C (2 : ℚ)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hα, sub_self]
  -- Since X³ - 2 is irreducible, it equals the minimal polynomial of α
  have heq : X ^ 3 - C (2 : ℚ) = minpoly ℚ α :=
    minpoly.eq_of_irreducible_of_monic X_cube_sub_two_irreducible heval
      (monic_X_pow_sub_C (2 : ℚ) (by norm_num))
  -- The minimal polynomial has degree 3
  have hndeg : (minpoly ℚ α).natDegree = 3 := by
    rw [← heq, natDegree_X_pow_sub_C]
  -- By the tower law, 3 = [ℚ(α):ℚ] divides [F:ℚ]
  have h3dvd : 3 ∣ Module.finrank ℚ F := hndeg ▸ minpoly.degree_dvd hint
  -- But [F:ℚ] = 2^k, so 3 ∣ 2^k
  rw [hk] at h3dvd
  -- Since 3 is prime and 3 ∣ 2^k, we get 3 ∣ 2 — a contradiction
  exact absurd ((by norm_num : Prime (3 : ℕ)).dvd_of_dvd_pow h3dvd) (by norm_num)
