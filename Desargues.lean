/-
  Desargues's Theorem (Wiedijk #87).

  We prove the algebraic form of Desargues's theorem: in the projective plane
  ℙ K K³ over any commutative ring K, if two triangles are in perspective from
  a point, they are in perspective from a line.

  Concretely: given vectors a b c o : Fin 3 → K and scalars sa ta sb tb sc tc,
  setting
    a' = sa • a + ta • o
    b' = sb • b + tb • o
    c' = sc • c + tc • o
  (A', B', C' lie on lines OA, OB, OC), the three "intersection" vectors
    P = (a ⨯₃ b) ⨯₃ (a' ⨯₃ b')    (on lines AB and A'B')
    Q = (a ⨯₃ c) ⨯₃ (a' ⨯₃ c')    (on lines AC and A'C')
    R = (b ⨯₃ c) ⨯₃ (b' ⨯₃ c')    (on lines BC and B'C')
  satisfy det [P, Q, R] = 0, i.e., P, Q, R are collinear in ℙ K K³.

  Proof outline:
    1. BAC–CAB: (u⨯v)⨯w = (u·w)v − (v·w)u gives
         P = det[a, a', b']·b − det[b, a', b']·a
    2. Multilinearity:
         det[a, sa·a+ta·o, sb·b+tb·o] = −ta·sb · det[a,b,o]
         det[b, sa·a+ta·o, sb·b+tb·o] = −sa·tb · det[a,b,o]
       so P = det[a,b,o] · (sa·tb·a − ta·sb·b), similarly Q, R.
    3. det[D·P', E·Q', F·R'] = D·E·F · det[P', Q', R'].
    4. det[P', Q', R'] = 0: the 3×3 coefficient matrix has det = 0 (ring identity).
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Matrix

-- ============================================================
-- STEP 1: DETERMINANT MULTILINEARITY LEMMAS
-- ============================================================

/-- det[a, sa·a+ta·o, sb·b+tb·o] = −ta·sb · det[a,b,o] -/
private lemma det_row1_lin [CommRing K] (a b o : Fin 3 → K) (sa ta sb tb : K) :
    Matrix.det ![ a, sa • a + ta • o, sb • b + tb • o] = -(ta * sb) * Matrix.det ![ a, b, o] := by
  rw [det_fin_three, det_fin_three]
  dsimp only [Matrix.cons_val]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- det[b, sa·a+ta·o, sb·b+tb·o] = −sa·tb · det[a,b,o] -/
private lemma det_row2_lin [CommRing K] (a b o : Fin 3 → K) (sa ta sb tb : K) :
    Matrix.det ![ b, sa • a + ta • o, sb • b + tb • o] = -(sa * tb) * Matrix.det ![ a, b, o] := by
  rw [det_fin_three, det_fin_three]
  dsimp only [Matrix.cons_val]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

-- ============================================================
-- STEP 2: FACTORED FORMS OF P, Q, R
-- ============================================================

/-- P = (a⨯b)⨯(a'⨯b') = det[a,b,o] · (sa·tb·a − ta·sb·b) -/
private lemma factP [CommRing K] (a b o : Fin 3 → K) (sa ta sb tb : K) :
    (a ⨯₃ b) ⨯₃ ((sa • a + ta • o) ⨯₃ (sb • b + tb • o)) =
    Matrix.det ![ a, b, o] • ((sa * tb) • a - (ta * sb) • b) := by
  have h1 : Matrix.det ![ a, sa • a + ta • o, sb • b + tb • o] =
      -(ta * sb) * Matrix.det ![ a, b, o] := det_row1_lin a b o sa ta sb tb
  have h2 : Matrix.det ![ b, sa • a + ta • o, sb • b + tb • o] =
      -(sa * tb) * Matrix.det ![ a, b, o] := det_row2_lin a b o sa ta sb tb
  rw [cross_cross_eq_smul_sub_smul]
  simp only [triple_product_eq_det]
  rw [h1, h2]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
  ring

/-- Q = (a⨯c)⨯(a'⨯c') = det[a,c,o] · (sa·tc·a − ta·sc·c) -/
private lemma factQ [CommRing K] (a c o : Fin 3 → K) (sa ta sc tc : K) :
    (a ⨯₃ c) ⨯₃ ((sa • a + ta • o) ⨯₃ (sc • c + tc • o)) =
    Matrix.det ![ a, c, o] • ((sa * tc) • a - (ta * sc) • c) := by
  have h1 : Matrix.det ![ a, sa • a + ta • o, sc • c + tc • o] =
      -(ta * sc) * Matrix.det ![ a, c, o] := det_row1_lin a c o sa ta sc tc
  have h2 : Matrix.det ![ c, sa • a + ta • o, sc • c + tc • o] =
      -(sa * tc) * Matrix.det ![ a, c, o] := det_row2_lin a c o sa ta sc tc
  rw [cross_cross_eq_smul_sub_smul]
  simp only [triple_product_eq_det]
  rw [h1, h2]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
  ring

/-- R = (b⨯c)⨯(b'⨯c') = det[b,c,o] · (sb·tc·b − tb·sc·c) -/
private lemma factR [CommRing K] (b c o : Fin 3 → K) (sb tb sc tc : K) :
    (b ⨯₃ c) ⨯₃ ((sb • b + tb • o) ⨯₃ (sc • c + tc • o)) =
    Matrix.det ![ b, c, o] • ((sb * tc) • b - (tb * sc) • c) := by
  have h1 : Matrix.det ![ b, sb • b + tb • o, sc • c + tc • o] =
      -(tb * sc) * Matrix.det ![ b, c, o] := det_row1_lin b c o sb tb sc tc
  have h2 : Matrix.det ![ c, sb • b + tb • o, sc • c + tc • o] =
      -(sb * tc) * Matrix.det ![ b, c, o] := det_row2_lin b c o sb tb sc tc
  rw [cross_cross_eq_smul_sub_smul]
  simp only [triple_product_eq_det]
  rw [h1, h2]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
  ring

-- ============================================================
-- STEP 3: ROW SCALING MULTIPLIES THE DETERMINANT
-- ============================================================

/-- det[D·P', E·Q', F·R'] = D·E·F · det[P', Q', R'] -/
private lemma det_smul_rows [CommRing K] (D E F : K) (P' Q' R' : Fin 3 → K) :
    Matrix.det ![ D • P', E • Q', F • R'] = D * E * F * Matrix.det ![ P', Q', R'] := by
  rw [det_fin_three, det_fin_three]
  dsimp only [Matrix.cons_val]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

-- ============================================================
-- STEP 4: THE COEFFICIENT MATRIX HAS ZERO DETERMINANT
-- ============================================================

/-- det[sa·tb·a − ta·sb·b, sa·tc·a − ta·sc·c, sb·tc·b − tb·sc·c] = 0.

    The coefficient matrix
      | sa·tb  −ta·sb    0    |
      | sa·tc    0    −ta·sc  |
      |   0    sb·tc  −tb·sc  |
    has det = sa·ta·sb·tb·sc·tc − sa·ta·sb·tb·sc·tc = 0. -/
private lemma det_coeff_zero [CommRing K] (a b c : Fin 3 → K) (sa ta sb tb sc tc : K) :
    Matrix.det ![ (sa * tb) • a - (ta * sb) • b,
                  (sa * tc) • a - (ta * sc) • c,
                  (sb * tc) • b - (tb * sc) • c] = 0 := by
  rw [det_fin_three]
  dsimp only [Matrix.cons_val]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

-- ============================================================
-- MAIN THEOREM: DESARGUES'S THEOREM
-- ============================================================

/-- **Desargues's Theorem** (Wiedijk #87).

    In the projective plane ℙ K K³ over a commutative ring K, if two triangles
    are in perspective from a point, they are in perspective from a line.

    Algebraically: for vectors a b c o : Fin 3 → K and scalars sa ta sb tb sc tc : K,
    let a' = sa·a + ta·o, b' = sb·b + tb·o, c' = sc·c + tc·o
    (placing A', B', C' on lines OA, OB, OC respectively). Then the vectors
        P = (a ⨯₃ b) ⨯₃ (a' ⨯₃ b'),
        Q = (a ⨯₃ c) ⨯₃ (a' ⨯₃ c'),
        R = (b ⨯₃ c) ⨯₃ (b' ⨯₃ c')
    (representing intersection points of corresponding sides) are collinear:
        det [P, Q, R] = 0.

    Proof: Factor P = det[a,b,o] · P', Q = det[a,c,o] · Q', R = det[b,c,o] · R'
    (via the BAC–CAB identity and det multilinearity), then det[P',Q',R'] = 0
    by an explicit 3×3 ring computation. -/
theorem desargues_theorem [CommRing K] (a b c o : Fin 3 → K) (sa ta sb tb sc tc : K) :
    Matrix.det
      ![(a ⨯₃ b) ⨯₃ ((sa • a + ta • o) ⨯₃ (sb • b + tb • o)),
        (a ⨯₃ c) ⨯₃ ((sa • a + ta • o) ⨯₃ (sc • c + tc • o)),
        (b ⨯₃ c) ⨯₃ ((sb • b + tb • o) ⨯₃ (sc • c + tc • o))] = 0 := by
  rw [factP a b o sa ta sb tb, factQ a c o sa ta sc tc, factR b c o sb tb sc tc,
      det_smul_rows, det_coeff_zero, mul_zero]
