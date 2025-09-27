import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Algebra.Order.Module.PositiveLinearMap
-- Mathlib.Algebra.Star.StarRingHom
import Mathlib.Topology.Defs.Filter
import Mathlib.Data.Set.Operations
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.Star -- conjugate linear maps
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Order

example {a b : ℚ} (h1 : a ≤ 1) (h2 : b ≤ 3) : (a + b) / 2 ≤ 2 := by
  linear_combination (h1 + h2) / 2

open ComplexConjugate
open scoped ComplexOrder
scoped[ComplexOrder] attribute [instance] Complex.partialOrder -- this is very important
open Complex
open Mathlib.Tactic.LinearCombination

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)
-- LinearMap (starRingEnd R) M M₂
variable (p : A) (q : A) -- for experimentation. remove later
set_option linter.unusedSectionVars false -- remove this at the end

/-def myf (f : A →ₚ[ℂ] ℂ) : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ A).comp (starLinearEquiv ℂ (A := A) : A →ₗ⋆[ℂ] A) |>.compr₂ₛₗ f
-/
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
  rw [← h]
  assumption

-- instance {F : Type*} [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂] [OrderHomClass F A₁ A₂] :
--    StarHomClass F A₁ A₂
-- should give:
open PositiveLinearMap
theorem aupetit_6_2_15i (x : A) : f (star x) = conj (f x) := by simp [map_star]

lemma fOfxStarxIsReal (x : A) : (f (x * star x)).re = f (x * star x) := by
  have xstarmul : star (x * star x) = x * star x := by exact star_mul_star x x
  have fstareqfnostar : f (star (x * star x)) = f (x * star x)
    := by exact congrArg (⇑f) xstarmul
  have fstareqconj: f (star (x * star x)) = conj (f (x * star x))
    := by exact aupetit_6_2_15i f (x * star x)
  rw [fstareqconj] at fstareqfnostar
  have fxisreal := Complex.conj_eq_iff_re.mp fstareqfnostar
  exact fxisreal

lemma fxx_eq_conj (x : A) : conj (f (x * star x)) = f (x * star x) :=
  conj_eq_iff_re.mpr (fOfxStarxIsReal f x)

lemma fOfxStarxHas0Im (x : A) : (f (x * star x)).im = 0 := by
  have xstarmul : star (x * star x) = x * star x := by exact star_mul_star x x
  have fstareqfnostar : f (star (x * star x)) = f (x * star x)
    := by exact congrArg (⇑f) xstarmul
  have fstareqconj: f (star (x * star x)) = conj (f (x * star x))
    := by exact aupetit_6_2_15i f (x * star x)
  rw [fstareqconj] at fstareqfnostar
  have fxisreal := Complex.conj_eq_iff_im.mp fstareqfnostar
  exact fxisreal

example (c : ℂ) : norm c ^ 2 = c * conj c := by exact Eq.symm (mul_conj' c)

lemma aupetit_6_2_15iilemma (t : ℂ) (ht : t = conj t) (x y : A) (h : f (x * star y) ≠ 0) :
  -- initally did the proof with (t : ℝ), but then when I changed it, it immediately hilighted
  -- the step that failed, so I could go, rigirously repair the proof step by step
  -- TO-DO: re-write with a calculation proof
  0 ≤ f (x * star x) + 2 * t * norm (f (x * star y)) + t^2 * f (y * star y) := by
  have := aupetit_6_2_15lemma f x y ((t * f (x * star y))/(norm (f (x * star y))))
  have fact := mul_conj' (f (x * star y))
  have fact2 : f (y * star x) = f (star (x * star y)) := by simp
  have fact3 : f (star (x * star y)) = conj (f (x * star y)) := aupetit_6_2_15i (f) (x * star y)
  have fact4 : f (y * star x) = conj (f (x * star y)) := Eq.trans fact2 fact3
  simp [fact4] at this
  have fact5 : ↑t * f (x * star y) / ↑‖f (x * star y)‖ * (starRingEnd ℂ) (f (x * star y)) =
    ↑t * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))) / ↑‖f (x * star y)‖ := by field_simp
  simp [fact] at fact5
  have fact6 : (t : ℂ) * ↑‖f (x * star y)‖ ^ 2 / ↑‖f (x * star y)‖ = ↑t * ↑‖f (x * star y)‖ := by
    field_simp
  have fact7 :=  Eq.trans fact5 fact6
  simp [fact7] at this
  have fact8 : ↑t * (starRingEnd ℂ) (f (x * star y)) / ↑‖f (x * star y)‖ * f (x * star y) =
    ↑t * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))) / ↑‖f (x * star y)‖ := by ring
  simp [fact] at fact8
  have fact9 : (t : ℂ) * ↑‖f (x * star y)‖ ^ 2 / ↑‖f (x * star y)‖ = ↑t * ↑‖f (x * star y)‖ := by
    field_simp
  have fact10 := Eq.trans fact8 fact9
  rw [ht] at this
  simp [fact10] at this
  have fact11 :
    ↑t * f (x * star y) / ↑‖f (x * star y)‖ *
      (↑t * (starRingEnd ℂ) (f (x * star y)) / ↑‖f (x * star y)‖) *
      f (y * star y) =
      (↑t^2 * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))))/ ↑‖f (x * star y)‖ ^ 2 *
      f (y * star y) := by field_simp
  rw [← ht] at this
  rw [fact11] at this
  simp [fact] at this
  field_simp at this
  nth_rw 2 [add_assoc] at this
  rw [← two_mul, ← mul_assoc] at this
  exact this

noncomputable def c : ℝ := 1 + (2:ℝ)^(1/2 : ℝ)

theorem aupetit_6_2_15ii (x y : A) :
  norm (f (x * star y)) ^ 2 ≤ f (x * star x) * f (y * star y) := by
  -- have h := aupetit_6_2_15lemma f x y (f (x * star y)/((1+2^(1/2))*f (y * star y)))
  have fxisreal := fOfxStarxIsReal f x
  have fyisreal := fOfxStarxIsReal f y
  have fxx := fxx_eq_conj f x
  have fyy := fxx_eq_conj f y
  have fxnonneg := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg x)
  have fynonneg := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg y)
  have cRealSelf: (c : ℂ).re  = c := by exact rfl
  have fyyIm0: (f (y * star y)).im  = 0 := by exact fOfxStarxHas0Im f y
  have fxxIm0: (f (x * star x)).im  = 0 := by exact fOfxStarxHas0Im f x
  have constEqOwnConj : conj (c : ℂ) = c := by simp
  have constIm0 : (c : ℂ).im = 0 := by exact conj_eq_iff_im.mp constEqOwnConj

  /-have prodreal :
    (1 + (2:ℝ)^(1/2 : ℝ))*f (y * star y) = conj ((1 + (2:ℝ)^(1/2 : ℝ))*f (y * star y)) := by exact?
  -/

  have prodIm0 : (c*f (y * star y)).im = 0 := by
    simp; right
    exact fyyIm0
  have invIm0 : ((c*f (y * star y))⁻¹).im = 0 := by
    simp [Complex.inv_im]
    left; left
    exact fyyIm0

  /- -- this works. I should have realize sooner, but also this should not be true >:(
  have : 1 + 2^(1/2) = 1 + 1 := by simp-/

  have normIm0 : (norm (f (x * star y)) :ℂ ).im = 0 := by exact rfl
  have fullProdIm0 := Complex.smul_im ((norm (f (x * star y)))) (c * f (y * star y))⁻¹

  rw [invIm0, MulActionWithZero.smul_zero ‖f (x * star y)‖] at fullProdIm0
  have eqOwnConj : (‖f (x * star y)‖ • (c * f (y * star y))⁻¹)
   = conj (‖f (x * star y)‖ • (c * f (y * star y))⁻¹) :=
     Eq.symm ((fun {z} ↦ conj_eq_iff_im.mpr) fullProdIm0)
  have inter := aupetit_6_2_15iilemma (f)
    (norm (f (x * star y))/(c*f (y * star y))) eqOwnConj x y
  by_cases fzero : f (x * star y) = 0
  · simp only [fzero, norm_zero, ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ge_iff_le]
    exact Left.mul_nonneg fxnonneg fynonneg
  push_neg at fzero
  have h := inter fzero
  simp at h
  rw [add_assoc, add_comm] at h
  have step1 := tsub_le_iff_right.mpr h
  rw [zero_sub] at step1
  have step2 := by calc
    -f (x * star x) ≤
  2 * (↑‖f (x * star y)‖ / (↑c * f (y * star y))) * ↑‖f (x * star y)‖ +
    (↑‖f (x * star y)‖ / (↑c * f (y * star y))) ^ 2 * f (y * star y) := step1
    _ = 2 * (↑‖f (x * star y)‖ / (↑c * f (y * star y))) * ↑‖f (x * star y)‖ +
    (↑‖f (x * star y)‖^2 / (↑c^2 * (f (y * star y))^2)) * f (y * star y) := by ring
    _ = 2 * (↑‖f (x * star y)‖ / (↑c * f (y * star y))) * ↑‖f (x * star y)‖ +
    (‖f (x * star y)‖^2 / (c^2 * (f (y * star y))))*((f (y * star y))⁻¹ * f (y * star y)) := by ring
    _ = 2 * (↑‖f (x * star y)‖ / (↑c * f (y * star y))) * ↑‖f (x * star y)‖ +
    (‖f (x * star y)‖^2 / (c^2 * (f (y * star y)))) := by field_simp
    _ = 2 * (↑‖f (x * star y)‖ / (↑c * f (y * star y))) * ↑‖f (x * star y)‖ +
    (‖f (x * star y)‖^2 / ((f (y * star y))* c^2)) := by ring
    _ = 2 * (↑‖f (x * star y)‖ / (↑c * f (y * star y))) * ↑‖f (x * star y)‖ +
    (‖f (x * star y)‖^2 / ((f (y * star y))* c))  / c := by ring
    _ = 2 * (↑‖f (x * star y)‖ / (↑c * f (y * star y))) * ↑‖f (x * star y)‖ +
    (‖f (x * star y)‖^2 / ((f (y * star y))* c)) * (1/c) := by ring
    _ = 2 * (‖f (x * star y)‖^2 / (↑c * f (y * star y))) +
            (‖f (x * star y)‖^2 / ((f (y * star y))* c)) * (1/c) := by ring
    _ = (2/c) * (‖f (x * star y)‖^2 / (f (y * star y))) +
        (1/c^2) * (‖f (x * star y)‖^2 / ((f (y * star y)))) := by ring
    _ = ((2/c) + (1/c^2)) * (‖f (x * star y)‖^2 / ((f (y * star y)))) := by ring
    _ = ((2*c/c^2) + (1/c^2)) * (‖f (x * star y)‖^2 / ((f (y * star y)))) := by field_simp
    _ = (((2*c+1)/c^2)) * (‖f (x * star y)‖^2 / ((f (y * star y)))) := by field_simp
    _ = 1 * (‖f (x * star y)‖^2 / ((f (y * star y)))) := by
        dsimp [c]
        rw [pow_two]
        norm_cast
        rw [mul_add, mul_add, add_mul, one_mul, mul_one, mul_one, add_mul, one_mul]
        have lem := pow_two ((2:ℝ)^((1:ℝ)/(2:ℝ)))
        rw [← lem]
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
        nth_rw 2 [add_assoc, ← add_assoc]
        rw [← two_mul, ← add_assoc]
        rw [add_assoc]
        nth_rw 2 [add_comm]
        rw [add_comm]
        congr
        · field_simp
        norm_num
      _ = ‖f (x * star y)‖^2 / ((f (y * star y))) := by rw [one_mul]
  by_cases fyyzero : f (y * star y) = 0
  · sorry
  push_neg at fyyzero
  have step3 : -f (x * star x) * (f (y * star y)) ≤
    ↑‖f (x * star y)‖ ^ 2 * (f (y * star y))⁻¹ * ((f (y * star y))) :=
      mul_le_mul_of_nonneg_right step2 fynonneg
  rw [mul_assoc] at step3
  nth_rw 3 [mul_comm] at step3
  rw [Complex.mul_inv_cancel fyyzero, mul_one] at step3
  have step4 := neg_le_neg step3
  sorry








      /-
       dsimp [c]; congr
      have l1 :
        Complex.ofReal (1 + (2:ℝ)^(1/2 : ℝ)) = (1 : ℂ) + ((2:ℝ)^(1/2 : ℝ) : ℂ) := by sorry
      rw [l1]

        have : ((2:NNReal)^(1/2 : ℝ)) ^ (2: ℝ) = 2 := by
          rw [← (NNReal.rpow_mul 2 (1/2) (2:ℝ))]
          field_simp
          norm_num
        have twopos : (2 : ℝ) = (2 : NNReal) := by exact rfl
        nth_rw 17 [twopos]
        norm_cast
        rw [this]-/




      /-
      change
      rw [c] at cRealSelf; dsimp [c];-- dsimp [Complex.ofReal_def]
      apply Complex.ext_iff.mpr
      constructor
      . rw [cRealSelf]; exact?
        -/




  /-have step2 := by calc
    0 - f (x * star x) ≤
    2 * (↑‖f (x * star y)‖ / (2 * f (y * star y))) * ↑‖f (x * star y)‖ +
      (↑‖f (x * star y)‖ / (2 * f (y * star y))) ^ 2 * f (y * star y) := step1
    _ =
    (2 * ↑‖f (x * star y)‖ / (2 * f (y * star y))) * ↑‖f (x * star y)‖ +
      (↑‖f (x * star y)‖ / (2 * f (y * star y))) ^ 2 * f (y * star y) := by ring
    _ =
    (↑‖f (x * star y)‖ / (f (y * star y))) * ↑‖f (x * star y)‖ +
      (↑‖f (x * star y)‖ / (2 * f (y * star y))) ^ 2 * f (y * star y) := by ring
    _ =
    (↑‖f (x * star y)‖^2 / (f (y * star y))) +
      (↑‖f (x * star y)‖ / (2 * f (y * star y))) ^ 2 * f (y * star y) := by ring
    _ =
    (↑‖f (x * star y)‖^2 / (f (y * star y))) +
      (↑‖f (x * star y)‖^2 / (2 * f (y * star y)) ^ 2) * f (y * star y) := by ring
    _ =
    (↑‖f (x * star y)‖^2 / (f (y * star y))) +
      (↑‖f (x * star y)‖^2 / ((2^2) * (f (y * star y))^2)) * f (y * star y) := by ring
    _ =
    (↑‖f (x * star y)‖^2 / (f (y * star y))) +
      (↑‖f (x * star y)‖^2 / ((2^2) * (f (y * star y)))) := by field_simp
    _ =
    ((↑‖f (x * star y)‖^2) +
      (↑‖f (x * star y)‖^2 / ((2^2)))) / (f (y * star y)) := by field_simp
    _ =
    ((↑‖f (x * star y)‖^2) + (↑‖f (x * star y)‖^2 / (4))) / (f (y * star y)) := by norm_num
    _ =
    ((4 * ↑‖f (x * star y)‖^2)/4 + (↑‖f (x * star y)‖^2 / (4))) / (f (y * star y)) := by norm_num
    _ =
    ((5 * ↑‖f (x * star y)‖^2 / (4))) / (f (y * star y)) := by ring
    _ =
    (((5/4) * ↑‖f (x * star y)‖^2)) / (f (y * star y)) := by ring
    _ =
    (((5/4) * ↑‖f (x * star y)‖^2)) * (f (y * star y))⁻¹ := by ring

  rw [zero_sub] at step2
  -- auptetit is missing the case because his proof is bad
  by_cases fyyzero : f (y * star y) = 0
  · sorry
  push_neg at fyyzero
  have step3 : -f (x * star x) * (f (y * star y)) ≤
    5 / 4 * ↑‖f (x * star y)‖ ^ 2 * (f (y * star y))⁻¹ * ((f (y * star y))) :=
      mul_le_mul_of_nonneg_right step2 fynonneg
  have step4 := by calc
   -f (x * star x) * (f (y * star y)) ≤
    5 / 4 * ↑‖f (x * star y)‖ ^ 2 * (f (y * star y))⁻¹ * ((f (y * star y))) := by exact
      step3
    _ = 5 / 4 * ↑‖f (x * star y)‖ ^ 2 * ((f (y * star y))⁻¹ * ((f (y * star y)))) := by ring
    _ = 5 / 4 * ↑‖f (x * star y)‖ ^ 2 * 1 := by
      congr
      rw [mul_comm]
      exact Complex.mul_inv_cancel fyyzero
    _ = 5 / 4 * ↑‖f (x * star y)‖ ^ 2 := by rw [mul_one]
  have step5 := neg_le_neg step4
  simp at step5

  have : 0 ≤ ‖f (x * star y)‖ := by exact norm_nonneg (f (x * star y))
  have hyp1 : 0 ≤ ‖f (x * star y)‖ ^ 2 := by exact sq_nonneg ‖f (x * star y)‖
  -/



  /-
  have hyp3 : (0: ℂ) ≤ ‖f (x * star y)‖ ^ 2 := by exact hyp1
  have hyp2 : (0 : ℂ) ≤ (5/4 : ℂ) := by sorry
  have hyp4 : (0 : ℂ)  ≤ ((5/4) * ‖f (x * star y)‖^2) := by exact mul_nonneg hyp2 hyp3
  #check mul_le_of_le_div₀ hyp4 fynonneg
  have : -f (x * star x) * f (y * star y) ≤ (↑‖f (x * star y)‖ ^ 2 + ↑‖f (x * star y)‖ ^ 2 / 4) := by exact?

  -/


  /-
  rcases fullProdIm0 with h1 | h2 | h3
  . have two_ne_zero : 2 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one 1)
    rw [h1, norm_zero]
    norm_num
    exact Left.mul_nonneg fxnonneg fynonneg
  . have eqOwnConj : (norm (f (x * star y))) (((1 + 2^(1/2))*f (y * star y))⁻¹) =
      conj (norm (f (x * star y))) (((1 + 2^(1/2))*f (y * star y))⁻¹) := by exact?
    have inter := aupetit_6_2_15iilemma (f) (norm (f (x * star y))/((1 + 2^(1/2))*f (y * star y))) eqOwnConj x y
  sorry
  -/
  /-
  have eqOwnConj :
  have
    aupetit_6_2_15iilemma (f) (norm (f (x * star y))/((1 + 2^(1/2))*f (y * star y))) eqOwnConj x y
    fzero

  rw [add_assoc, add_comm] at subst
  have step1 := tsub_le_iff_right.mpr subst
  simp at step1
  norm_num at step1
  rw [← mul_assoc] at step1
  nth_rw 1 [mul_assoc] at step1
  have step2 := by calc
    -f (x * star x) ≤
  2 * (↑‖f (x * star y)‖ / 2) * (f (y * star y) * ↑‖f (x * star y)‖) +
    (↑‖f (x * star y)‖ / 2 * f (y * star y)) ^ 2 * f (y * star y) := step1
    _ = ‖f (x * star y)‖ * (f (y * star y) * ↑‖f (x * star y)‖) +
    (↑‖f (x * star y)‖ / 2 * f (y * star y)) ^ 2 * f (y * star y) := by congr; field_simp
    _ = ‖f (x * star y)‖^2 * f (y * star y) +
    (↑‖f (x * star y)‖ / 2 * f (y * star y)) ^ 2 * f (y * star y) := by ring
    _ = ‖f (x * star y)‖^2 * f (y * star y) +
    (↑‖f (x * star y)‖ / 2)^2 * f (y * star y)) ^ 2 * f (y * star y) := by ring
  -/


  sorry


-- Begin code from Eric Wieser
-- noncomputability should be fixed in by Eric Wieser's bug fix
noncomputable def mySesquilinear (f : A →ₚ[ℂ] ℂ) : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ A).comp (starLinearEquiv ℂ (A := A) : A →ₗ⋆[ℂ] A) |>.compr₂ₛₗ f

@[simp]
theorem mySesquilinear_apply (f : A →ₚ[ℂ] ℂ) (x y : A) :
  mySesquilinear f x y = f (star x * y) := rfl
-- End code from Eric Wieser

lemma add_mem_helper (f : A →ₚ[ℂ] ℂ) (a b : A) : a ∈ {a | f (star a * a) = 0}
  → b ∈ {a | f (star a * a) = 0} → a + b ∈ {a | f (star a * a) = 0} := by
  simp
  intro h1 h2
  rw [mul_add, add_mul, add_mul, ← add_assoc]
  have : f (star a * a + star b * a + star a * b + star b * b)
    = f (star a * a) + f (star b * a) + f (star a * b) + f (star b * b) := by simp
  rw [this]
  rw [h1, h2]
  ring_nf
  sorry

lemma myCS (f : A →ₚ[ℂ] ℂ) (a b : A) :
  norm (f (star b * a)) ^ 2 ≤ f (star b * b) * f (star a * a) := by
  rw [← mySesquilinear_apply f a a, ← mySesquilinear_apply f b b, ← mySesquilinear_apply f b a]
  sorry

lemma smul_mem_helper (f : A →ₚ[ℂ] ℂ) (b : A) {a : A} : a ∈ {a | f (star a * a) = 0}
  → b • a ∈ {a | f (star a * a) = 0} := by
  rw [Set.mem_setOf, Set.mem_setOf]
  intro h
  #check mySesquilinear_apply f a a
  rw [← mySesquilinear_apply f a a] at h
  rw [← mySesquilinear_apply f (b • a) (b • a)]
  sorry

-- From Aupetit leamm 6.2.18
-- should probably use module ideal? see 10.1.1 MIL
def N (f : A →ₚ[ℂ] ℂ) : Ideal A where
  carrier := {a : A | f (star a * a) = 0}
  add_mem' := by intro a b; exact add_mem_helper f a b
  zero_mem' := by simp;
  smul_mem' := by intro b; exact smul_mem_helper f b

--theorem aupetit6_2_18_closed : IsClosed {a : A | f (star a * a) = 0} := by sorry
variable (f : A →ₚ[ℂ] ℂ)
#check N f
#check Ideal.coe_closure (N f)
#check (N f).closure
#check ((N f) : Set A)

theorem aupetit6_2_18_closed' : (N f) = (N f).closure := by sorry

theorem aupetit6_2_18_closed : IsClosed ((N f) : Set A) := by sorry

/-
To-do: define A/N f, and the inner product on it
- define the semi-inner product/positive semidefinite sesquilinar form, from 138 8.0.10
- or maybe define the full inner product from 8.0.14
- set up all relevant statements with sorries first
- maybe refactor so that the ideal definition is actually easy to prove
- make the partial order on the CStarAlgebra explicit so that I can use
  non-negativity of certain elements, like a* a (I think StarOrderedRing does this)
- enable the better star notation
-/

/-
Graveyard:

    -- have refxnonneg := fxnonneg
    -- rw [← fxisreal] at refxnonneg
    -- have zisz : (0 : ℂ) = (0 : ℝ) := by exact rfl
    -- rw [zisz, ← fxisreal] at fxnonneg
    -- rw [← fxisreal, ← fyisreal]

    -- have fxim0 : (f (x * star x)).im = (0 : ℝ) := by exact fOfxStarxHas0Im f x
    -- have fyim0 : (f (y * star y)).im = (0 : ℝ) := by exact fOfxStarxHas0Im f y
    -- have fximeqfyim := fxim0
    -- rw [← fyim0] at fximeqfyim
    -- #check Complex.le_def.mp fxnonneg
-/
