import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

open ComplexConjugate
open scoped ComplexOrder
open Complex

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

lemma aupetit_6_2_15lemma (x y : A) (l : ℂ) :
  0 ≤ f (x * star x) + l * f (y * star x) + (conj l) * f (x * star y)
    + l * (conj l) * f (y * star y) := by
  have hnonneg :=  PositiveLinearMap.map_nonneg f (mul_star_self_nonneg (x + (l • y)))
  rw [add_mul, star_add, mul_add, mul_add] at hnonneg
  simp only [star_smul, RCLike.star_def, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, map_add,
    map_smul, smul_eq_mul] at hnonneg
  have h : f (x * star x) + (starRingEnd ℂ) l * f (x * star y)
      + (l * f (y * star x) + (starRingEnd ℂ) l * (l * f (y * star y)))
    = f (x * star x) + l * f (y * star x) + (starRingEnd ℂ) l * f (x * star y)
      + l * (starRingEnd ℂ) l * f (y * star y) := by ring
  rwa [← h]

theorem aupetit_6_2_15i (x : A) : f (star x) = conj (f x) := by simp [map_star]

lemma fOfxStarxIsReal (x : A) : (f (x * star x)).re = f (x * star x) := by
  have fstareqfnostar : f (star (x * star x)) = f (x * star x)
    := congrArg (⇑f) (star_mul_star x x)
  rw [(aupetit_6_2_15i f (x * star x))] at fstareqfnostar
  apply Complex.conj_eq_iff_re.mp fstareqfnostar

lemma fxx_eq_conj (x : A) : conj (f (x * star x)) = f (x * star x) :=
  conj_eq_iff_re.mpr (fOfxStarxIsReal f x)

lemma fOfxStarxHas0Im (x : A) : (f (x * star x)).im = 0 := by
  have fstareqfnostar : f (star (x * star x)) = f (x * star x)
    := congrArg (⇑f) (star_mul_star x x)
  rw [(aupetit_6_2_15i f (x * star x))] at fstareqfnostar
  apply Complex.conj_eq_iff_im.mp fstareqfnostar

lemma fact (x y : A) :
  f (x * star y) * conj (f (x * star y)) = ↑‖f (x * star y)‖ ^ 2 :=
  mul_conj' (f (x * star y))

lemma fact1 (x y : A) : f (y * star x) = conj (f (x * star y)) := calc
      f (y * star x) = f (star (x * star y)) := by simp
      _ = conj (f (x * star y)) := aupetit_6_2_15i (f) (x * star y)

lemma fact2 (x y : A) (t : ℂ) :
  t * f (x * star y) / ↑‖f (x * star y)‖ * (starRingEnd ℂ) (f (x * star y))
    = t * ↑‖f (x * star y)‖ := by
  calc
      ↑t * f (x * star y) / ↑‖f (x * star y)‖ * (starRingEnd ℂ) (f (x * star y)) =
    ↑t * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))) / ↑‖f (x * star y)‖ := by field_simp
    _ = t * ↑‖f (x * star y)‖ ^ 2 / ↑‖f (x * star y)‖ := by rw [fact f x y]
    _ = ↑t * ↑‖f (x * star y)‖ := by field_simp

lemma fact3 (x y : A) (t : ℂ) :
  t * (starRingEnd ℂ) (f (x * star y)) / ↑‖f (x * star y)‖ * f (x * star y)
    = t * ↑‖f (x * star y)‖ := calc
      ↑t * (starRingEnd ℂ) (f (x * star y)) / ↑‖f (x * star y)‖ * f (x * star y) =
    ↑t * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))) / ↑‖f (x * star y)‖ := by ring
      _ = t * ↑‖f (x * star y)‖ ^ 2 / ↑‖f (x * star y)‖ := by rw [fact]
      _ =  ↑t * ↑‖f (x * star y)‖  := by field_simp

lemma fact4 (x y : A) (t : ℂ) :
    ↑t * f (x * star y) / ↑‖f (x * star y)‖ *
      (↑t * (starRingEnd ℂ) (f (x * star y)) / ↑‖f (x * star y)‖) * f (y * star y) =
      (↑t^2 * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))))/ ↑‖f (x * star y)‖ ^ 2 *
        f (y * star y) := by field_simp

lemma aupetit_6_2_15iilemma (t : ℂ) (ht : t = conj t) (x y : A) (h : f (x * star y) ≠ 0) :
  0 ≤ f (x * star x) + 2 * t * norm (f (x * star y)) + t^2 * f (y * star y) := by
  have := aupetit_6_2_15lemma f x y ((t * f (x * star y))/(norm (f (x * star y))))
  rw [fact1 f x y, (fact2 (f) x y t), ht] at this
  simp [fact3 f x y t] at this
  rw [← ht, fact4 f x y t, fact] at this
  field_simp at this
  nth_rw 2 [add_assoc] at this
  rwa [← two_mul, ← mul_assoc] at this

lemma aupetit_6_2_15iilemma' (t : ℝ) (x y : A) (h : f (x * star y) ≠ 0) :
  0 ≤ f (x * star x) + 2 * t * norm (f (x * star y)) + t^2 * f (y * star y) :=
    aupetit_6_2_15iilemma f t (Eq.symm (conj_ofReal t)) x y h

-- Re-do with Cauchy-Schwarz
theorem aup_6_2_15ii (x y : A) : norm (f (x * star y)) ^ 2 ≤ f (x * star x) * f (y * star y) := by
  have fxnonneg := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg x)
  have fynonneg := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg y)

  by_cases fzero : f (x * star y) = 0
  · simp [fzero, (Left.mul_nonneg fxnonneg fynonneg)]
  push_neg at fzero
  by_cases fyyzero : f (y * star y) = 0
  · have twoEqConj : 2 = conj (2 : ℂ) := Eq.symm ((fun {z} ↦ conj_eq_iff_re.mpr) rfl)
    by_cases fxzero : f (x * star x) = 0
    · have normLeq0 := aupetit_6_2_15iilemma' (f) (-1/2) x y fzero
      rw [ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat, fxzero, fyyzero, zero_add,
        mul_zero, add_zero] at normLeq0
      norm_num at normLeq0
      have normGeq0 : 0 ≤ (norm (f (x * star y)) : ℂ) := by
        norm_cast; exact norm_nonneg (f (x * star y))
      have norm0 : 0 = (norm (f (x * star y)) : ℂ) := le_antisymm normGeq0 normLeq0
      simp [fxzero, fyyzero, ← norm0]
    let c := (2 * f (x * star x))/(-2 * norm (f (x * star y)))
    have constEqOwnConj : c = conj c := by
      dsimp [c]
      rw [neg_mul, map_div₀]
      norm_cast
      rw [conj_ofReal, map_mul (starRingEnd ℂ), fxx_eq_conj f x, ← twoEqConj]
    have h := aupetit_6_2_15iilemma (f) c constEqOwnConj x y fzero
    rw [fyyzero, mul_zero, add_zero] at h
    dsimp [c] at h
    field_simp at h
    norm_num at h
    have fxneg : f (x * star x) < 0 := lt_of_le_of_ne h fxzero
    linarith only [fxneg, fxnonneg]

  have invIm0 : ((f (y * star y))⁻¹).im = 0 := by
    rw [inv_im, div_eq_zero_iff, neg_eq_zero, map_eq_zero]
    left
    exact fOfxStarxHas0Im f y

  have fullProdIm0 := Complex.smul_im (-‖f (x * star y)‖) (f (y * star y))⁻¹
  rw [invIm0, MulActionWithZero.smul_zero (-‖f (x * star y)‖)] at fullProdIm0

  have eqOwnConj : (- ‖f (x * star y)‖ • (f (y * star y))⁻¹)
    = conj (- ‖f (x * star y)‖ • (f (y * star y))⁻¹) :=
      Eq.symm ((fun {z} ↦ conj_eq_iff_im.mpr) fullProdIm0)

  have inter := aupetit_6_2_15iilemma (f)
    (-‖f (x * star y)‖ • (f (y * star y))⁻¹) eqOwnConj x y

  have h := inter fzero
  rw [neg_smul, real_smul, mul_neg, neg_mul, Even.neg_pow (even_two), add_assoc, add_comm] at h

  have id1 := by calc
    - f (x * star x) = 0 - f (x * star x) := by ring
    _ ≤ -(2 * (‖f (x * star y)‖ / (f (y * star y))) * ↑‖f (x * star y)‖) +
    (‖f (x * star y)‖ / (f (y * star y))) ^ 2 * f (y * star y) := tsub_le_iff_right.mpr h
    _ = -(2 * (‖f (x * star y)‖^2 / (f (y * star y)))) +
    ((‖f (x * star y)‖^2) / ((f (y * star y)))) * (1/(f (y * star y))) * f (y * star y) := by ring
    _ = -(2 * (‖f (x * star y)‖^2 / (f (y * star y)))) +
    ((‖f (x * star y)‖^2) / ((f (y * star y)))) := by field_simp
    _ = (-(2 * (‖f (x * star y)‖^2)) +
    ((‖f (x * star y)‖^2))) * ((f (y * star y)))⁻¹ := by ring

  have id2 := by calc
    -f (x * star x) * f (y * star y) ≤  (-(2 * (‖f (x * star y)‖^2)) +
    ((‖f (x * star y)‖^2))) * ((f (y * star y)))⁻¹ * (f (y * star y)) :=
      mul_le_mul_of_nonneg_right id1 fynonneg
    _ = -(2 * ↑‖f (x * star y)‖ ^ 2) + ↑‖f (x * star y)‖ ^ 2 := by field_simp
    _ = (-2 + 1) * ↑‖f (x * star y)‖ ^ 2 := by ring
    _ = -1 * ↑‖f (x * star y)‖ ^ 2 := by norm_num

  have id3 := neg_le_neg id2
  rwa [neg_mul, one_mul, neg_neg, neg_mul, neg_neg] at id3

theorem aupetit_6_2_15iiia (x : A) : norm (f x) ^ 2 ≤ f (1 : A) * f (x * star x) := by
  have := aup_6_2_15ii f x (1 : A)
  rwa [star_one, mul_one, mul_one, mul_comm] at this
