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

lemma aupetit_6_2_15iilemma (t : ℂ) (ht : t = conj t) (x y : A) (h : f (x * star y) ≠ 0) :
  0 ≤ f (x * star x) + 2 * t * norm (f (x * star y)) + t^2 * f (y * star y) := by
  have := aupetit_6_2_15lemma f x y ((t * f (x * star y))/(norm (f (x * star y))))
  have fact := mul_conj' (f (x * star y))

  have fact1 : f (y * star x) = conj (f (x * star y)) := by
    calc
      f (y * star x) = f (star (x * star y)) := by simp
      _ = conj (f (x * star y)) := aupetit_6_2_15i (f) (x * star y)
  have fact2 := by
    calc
      ↑t * f (x * star y) / ↑‖f (x * star y)‖ * (starRingEnd ℂ) (f (x * star y)) =
    ↑t * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))) / ↑‖f (x * star y)‖ := by field_simp
    _ = t * ↑‖f (x * star y)‖ ^ 2 / ↑‖f (x * star y)‖ := by rw [fact]
    _ = ↑t * ↑‖f (x * star y)‖ := by field_simp
  have fact3 :=
    calc
      ↑t * (starRingEnd ℂ) (f (x * star y)) / ↑‖f (x * star y)‖ * f (x * star y) =
    ↑t * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))) / ↑‖f (x * star y)‖ := by ring
      _ = t * ↑‖f (x * star y)‖ ^ 2 / ↑‖f (x * star y)‖ := by rw [fact]
      _ =  ↑t * ↑‖f (x * star y)‖  := by field_simp

  rw [fact1, fact2, ht] at this
  simp [fact3] at this
  have fact4 :
    ↑t * f (x * star y) / ↑‖f (x * star y)‖ *
      (↑t * (starRingEnd ℂ) (f (x * star y)) / ↑‖f (x * star y)‖) * f (y * star y) =
      (↑t^2 * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))))/ ↑‖f (x * star y)‖ ^ 2 *
        f (y * star y) := by field_simp
  rw [← ht, fact4, fact] at this
  field_simp at this
  nth_rw 2 [add_assoc] at this
  rwa [← two_mul, ← mul_assoc] at this

theorem aup_6_2_15ii (x y : A) : norm (f (x * star y)) ^ 2 ≤ f (x * star x) * f (y * star y) := by
  have fxx := fxx_eq_conj f x
  have fxnonneg := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg x)
  have fynonneg := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg y)
  have fyyIm0: (f (y * star y)).im  = 0 := fOfxStarxHas0Im f y
  have fxxEqConj: f (x * star x)  = conj (f (x * star x)) := Eq.symm fxx
  have fullProdIm0 := Complex.smul_im (-‖f (x * star y)‖) (f (y * star y))⁻¹
  have invIm0 : ((f (y * star y))⁻¹).im = 0 := by
    rw [inv_im, div_eq_zero_iff, neg_eq_zero, map_eq_zero]
    left
    exact fyyIm0

  rw [invIm0, MulActionWithZero.smul_zero (-‖f (x * star y)‖)] at fullProdIm0
  have eqOwnConj : (- ‖f (x * star y)‖ • (f (y * star y))⁻¹)
   = conj (- ‖f (x * star y)‖ • (f (y * star y))⁻¹) :=
     Eq.symm ((fun {z} ↦ conj_eq_iff_im.mpr) fullProdIm0)

  have inter := aupetit_6_2_15iilemma (f)
    (-‖f (x * star y)‖ • (f (y * star y))⁻¹) eqOwnConj x y

  by_cases fzero : f (x * star y) = 0
  · rw [fzero, norm_zero, ofReal_zero]
    norm_num
    exact Left.mul_nonneg fxnonneg fynonneg
  have fzero2 := fzero
  by_cases fyyzero : f (y * star y) = 0
  · push_neg at fzero2
    have twoEqConj : 2 = conj (2 : ℂ) := Eq.symm ((fun {z} ↦ conj_eq_iff_re.mpr) rfl)
    by_cases fxzero : f (x * star x) = 0
    · have halfEqOwnConj : (-1/2 : ℂ) = conj (-1/2 : ℂ) := by
        rw [map_div₀, map_neg, map_one]
        congr
      have l1 := aupetit_6_2_15iilemma (f) (-1/2) halfEqOwnConj x y fzero2
      rw [fxzero, fyyzero] at l1
      have step : (0 : ℂ) ≤ - norm (f (x * star y)) := by
        calc
          (0 : ℂ) ≤ 0 + 2 * (- 1 / 2) * ↑‖f (x * star y)‖ + (- 1 / 2) ^ 2 * 0 := l1
          _ = - ↑‖f (x * star y)‖ := by
            rw [zero_add, mul_zero, add_zero]
            norm_num
      rw [fxzero, fyyzero, zero_mul]
      have normLeq0 : (norm (f (x * star y)) : ℂ) ≤ 0 := by exact neg_nonneg.mp step
      have := norm_nonneg (f (x * star y))
      have normGeq0 : 0 ≤ (norm (f (x * star y)) : ℂ) := by exact zero_le_real.mpr this
      have norm0 : 0 = (norm (f (x * star y)) : ℂ) := le_antisymm normGeq0 normLeq0
      rw [← norm0]
      simp
    let c := (2 * f (x * star x))/(-2 * norm (f (x * star y)))

    have constEqOwnConj : c = conj c := by
      dsimp [c]
      rw [neg_mul, map_div₀]
      norm_cast
      rw [conj_ofReal, map_mul (starRingEnd ℂ), ← fxxEqConj, ← twoEqConj]
    have := aupetit_6_2_15iilemma (f) c constEqOwnConj x y fzero2
    rw [fyyzero, mul_zero, add_zero] at this
    dsimp [c] at this
    field_simp at this
    norm_num at this
    have fxneg : f (x * star x) < 0 := lt_of_le_of_ne this fxzero
    linarith only [fxneg, fxnonneg]
  push_neg at fzero

  have h := inter fzero
  rw [neg_smul, real_smul, mul_neg, neg_mul, Even.neg_pow (even_two), add_assoc, add_comm] at h

  have step1 := tsub_le_iff_right.mpr h
  rw [zero_sub] at step1

  have step2 := by calc
    -f (x * star x) ≤
    -(2 * (‖f (x * star y)‖ / (f (y * star y))) * ↑‖f (x * star y)‖) +
    (‖f (x * star y)‖ / (f (y * star y))) ^ 2 * f (y * star y) := step1
    _ = -(2 * (‖f (x * star y)‖^2 / (f (y * star y)))) +
    ((‖f (x * star y)‖^2) / ((f (y * star y)))) * (1/(f (y * star y))) * f (y * star y) := by ring
    _ = -(2 * (‖f (x * star y)‖^2 / (f (y * star y)))) +
    ((‖f (x * star y)‖^2) / ((f (y * star y)))) := by field_simp
    _ = (-(2 * (‖f (x * star y)‖^2)) +
    ((‖f (x * star y)‖^2))) * ((f (y * star y)))⁻¹ := by ring

  have step3 : -f (x * star x) * (f (y * star y)) ≤
  (-(2 * (‖f (x * star y)‖^2)) +
    ((‖f (x * star y)‖^2))) * ((f (y * star y)))⁻¹ * (f (y * star y)) :=
      mul_le_mul_of_nonneg_right step2 fynonneg

  rw [mul_assoc] at step3
  nth_rw 4 [mul_comm] at step3
  rw [Complex.mul_inv_cancel fyyzero, mul_one] at step3
  have step4 := by calc
    -f (x * star x) * f (y * star y) ≤
      -(2 * ↑‖f (x * star y)‖ ^ 2) + ↑‖f (x * star y)‖ ^ 2 := step3
    _ = (-2 + 1) * ↑‖f (x * star y)‖ ^ 2 := by ring
    _ = -1 * ↑‖f (x * star y)‖ ^ 2 := by norm_num

  have step5 := neg_le_neg step4
  simp at step5
  exact step5

theorem aupetit_6_2_15iiia (x : A) : norm (f x) ^ 2 ≤ f (1 : A) * f (x * star x) := by
  have := aup_6_2_15ii f x (1 : A)
  rwa [star_one, mul_one, mul_one, mul_comm] at this

lemma aux (a b : A) (h : f (star a * a) = 0) : f (star a * b) = 0 := by
  have hab := aup_6_2_15ii f (star a) (star b)
  rw [star_star, star_star] at hab
  rw [h, zero_mul] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

def N (f : A →ₚ[ℂ] ℂ) : Submodule ℂ A where
  carrier := {a : A | f (star a * a) = 0}
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at ha
    rw [Set.mem_setOf_eq] at hb
    have hab := aux f a b ha
    have hba := aux f b a hb
    rw [Set.mem_setOf_eq, star_add, left_distrib, right_distrib, right_distrib,
      ← add_assoc, map_add, map_add, map_add, ha, hb, add_zero, zero_add, hba, hab, add_zero]
  zero_mem' := by simp;
  smul_mem' := by
    intro c x hx
    rw [Set.mem_setOf_eq] at hx
    rw [Set.mem_setOf_eq, star_smul, RCLike.star_def, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, map_smul, smul_eq_mul, mul_eq_zero, map_smul,
      smul_eq_mul, mul_eq_zero, map_eq_zero, or_self_left]
    right
    exact hx
