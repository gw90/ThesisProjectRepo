import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

open ComplexConjugate
open scoped ComplexOrder
scoped[ComplexOrder] attribute [instance] Complex.partialOrder -- this is very important
open Complex

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)
-- LinearMap (starRingEnd R) M M₂
variable (p : A) (q : A) -- for experimentation. remove later
-- set_option linter.unusedSectionVars false -- remove this at the end

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
  rwa [← h]

-- instance {F : Type*} [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂] [OrderHomClass F A₁ A₂] :
--    StarHomClass F A₁ A₂
-- should give:
open PositiveLinearMap
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

example (c : ℂ) : norm c ^ 2 = c * conj c := by exact Eq.symm (mul_conj' c)


-- initally did the proof with (t : ℝ), but then when I changed it, it immediately hilighted
-- the step that failed, so I could go, rigirously repair the proof step by step
lemma aupetit_6_2_15iilemma (t : ℂ) (ht : t = conj t) (x y : A) (h : f (x * star y) ≠ 0) :
  0 ≤ f (x * star x) + 2 * t * norm (f (x * star y)) + t^2 * f (y * star y) := by
  have := aupetit_6_2_15lemma f x y ((t * f (x * star y))/(norm (f (x * star y))))
  have fact := mul_conj' (f (x * star y))

  have fact1 : f (y * star x) = conj (f (x * star y)) := by
    calc
      f (y * star x) = f (star (x * star y)) := by simp
      _ = conj (f (x * star y)) := aupetit_6_2_15i (f) (x * star y)
  rw [fact1] at this

  have fact2 := by
    calc
      ↑t * f (x * star y) / ↑‖f (x * star y)‖ * (starRingEnd ℂ) (f (x * star y)) =
    ↑t * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))) / ↑‖f (x * star y)‖ := by field_simp
    _ = t * ↑‖f (x * star y)‖ ^ 2 / ↑‖f (x * star y)‖ := by rw [fact]
    _ = ↑t * ↑‖f (x * star y)‖ := by field_simp

  rw [fact2] at this

  have fact3 :=
    calc
      ↑t * (starRingEnd ℂ) (f (x * star y)) / ↑‖f (x * star y)‖ * f (x * star y) =
    ↑t * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))) / ↑‖f (x * star y)‖ := by ring
      _ = t * ↑‖f (x * star y)‖ ^ 2 / ↑‖f (x * star y)‖ := by rw [fact]
      _ =  ↑t * ↑‖f (x * star y)‖  := by field_simp

  rw [ht] at this
  simp [fact3] at this
  have fact4 :
    ↑t * f (x * star y) / ↑‖f (x * star y)‖ *
      (↑t * (starRingEnd ℂ) (f (x * star y)) / ↑‖f (x * star y)‖) *
      f (y * star y) =
      (↑t^2 * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))))/ ↑‖f (x * star y)‖ ^ 2 *
      f (y * star y) := by field_simp
  rw [← ht, fact4, fact] at this
  field_simp at this
  nth_rw 2 [add_assoc] at this
  rwa [← two_mul, ← mul_assoc] at this

theorem aupetit_6_2_15ii (x y : A) :
  norm (f (x * star y)) ^ 2 ≤ f (x * star x) * f (y * star y) := by
  have fxisreal := fOfxStarxIsReal f x
  have fyisreal := fOfxStarxIsReal f y
  have fxx := fxx_eq_conj f x
  have fyy := fxx_eq_conj f y
  have fxnonneg := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg x)
  have fynonneg := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg y)
  have fyyIm0: (f (y * star y)).im  = 0 := fOfxStarxHas0Im f y
  have fxxIm0: (f (x * star x)).im  = 0 := fOfxStarxHas0Im f x
  have fxxEqConj: f (x * star x)  = conj (f (x * star x)) := Eq.symm fxx

  have normIm0 : (norm (f (x * star y)) :ℂ ).im = 0 := rfl
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
  have := aupetit_6_2_15ii f x (1 : A)
  rwa [star_one, mul_one, mul_one, mul_comm] at this

-- From Aupetit leamm 6.2.18
-- should probably use module ideal? see 10.1.1 MIL
def M (f : A →ₚ[ℂ] ℂ) : Ideal A where
  carrier := {a : A | f (star a * a) = 0}
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at ha
    rw [Set.mem_setOf_eq] at hb
    rw [Set.mem_setOf_eq]
    rw [star_add, left_distrib, right_distrib, right_distrib, ← add_assoc]
    rw [map_add, map_add, map_add]
    rw [ha, hb, add_zero, zero_add]

    have hab := aupetit_6_2_15ii f (star a) (star b)
    rw [star_star, star_star] at hab
    rw [ha, hb, zero_mul] at hab
    norm_cast at hab
    rw [sq_nonpos_iff, norm_eq_zero] at hab


    have hba := aupetit_6_2_15ii f (star b) (star a)
    rw [star_star, star_star] at hba
    rw [ha, hb, zero_mul] at hba
    norm_cast at hba
    rw [sq_nonpos_iff, norm_eq_zero] at hba

    rw [hba, hab]
    norm_num -- could be simp too
  zero_mem' := by simp;
  smul_mem' := by
    intro c x hx
    rw [Set.mem_setOf_eq] at hx
    rw [Set.mem_setOf_eq]
    rw [smul_eq_mul, star_mul, ← mul_assoc]
    have := aupetit_6_2_15ii f (star x * star c * c) (star x)
    rw [star_star, star_mul, hx, mul_zero] at this
    norm_cast at this
    rw [sq_nonpos_iff, norm_eq_zero] at this
    assumption -- exact this

-- TO-DO: figure out if I'm using the right kind of Ideals/Quotients
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Quotient/Defs.html
-- I think I should maybe use module ideals/quotients because algebras extend vector spaces
-- Is that just a submodule? Is that what I really need?
-- https://leanprover-community.github.io/mathematics_in_lean/C10_Linear_Algebra.html#quotient-spaces

def N (f : A →ₚ[ℂ] ℂ) : Submodule ℂ A where
  carrier := {a : A | f (star a * a) = 0}
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at ha
    rw [Set.mem_setOf_eq] at hb
    rw [Set.mem_setOf_eq, star_add, left_distrib, right_distrib, right_distrib,
      ← add_assoc, map_add, map_add, map_add, ha, hb, add_zero, zero_add]

    have hab := aupetit_6_2_15ii f (star a) (star b)
    rw [star_star, star_star] at hab
    rw [ha, hb, zero_mul] at hab
    norm_cast at hab
    rw [sq_nonpos_iff, norm_eq_zero] at hab

    have hba := aupetit_6_2_15ii f (star b) (star a)
    rw [star_star, star_star] at hba
    rw [ha, hb, zero_mul] at hba
    norm_cast at hba
    rw [sq_nonpos_iff, norm_eq_zero] at hba

    rw [hba, hab]
    norm_num -- could be simp too
  zero_mem' := by simp;
  smul_mem' := by
    intro c x hx
    rw [Set.mem_setOf_eq] at hx
    rw [Set.mem_setOf_eq, star_smul, RCLike.star_def, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, map_smul, smul_eq_mul, mul_eq_zero, map_smul,
      smul_eq_mul, mul_eq_zero, map_eq_zero, or_self_left]
    right
    exact hx

-- Begin code from Eric Wieser
-- noncomputability should be fixed in by Eric Wieser's bug fix
noncomputable def mySesquilinear (f : A →ₚ[ℂ] ℂ) : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ A).comp (starLinearEquiv ℂ (A := A) : A →ₗ⋆[ℂ] A) |>.compr₂ₛₗ f

@[simp]
theorem mySesquilinear_apply (f : A →ₚ[ℂ] ℂ) (x y : A) :
  mySesquilinear f x y = f (star x * y) := rfl
-- End code from Eric Wieser

-- have to lift both the function and its inner function
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Quotient/Basic.html
-- use liftQ and mapQ

noncomputable instance myInnerProductSpace : InnerProductSpace.Core ℂ (A ⧸ N f) where
  inner a b := mySesquilinear f (Quotient.out a) (Quotient.out b)
  re_inner_nonneg := by
    intro a
    rw [mySesquilinear_apply, RCLike.re_to_complex]
    have := star_mul_self_nonneg (Quotient.out a)
    have := PositiveLinearMap.map_nonneg f this
    have := re_le_re this
    exact this
  definite := by
    intro a h
    rw [mySesquilinear_apply] at h
    have := (Submodule.Quotient.mk_eq_zero (N f)).mpr h
    rwa [Submodule.Quotient.mk_out] at this
  conj_inner_symm := by
    intro a b
    rw [mySesquilinear_apply]
    rw [← (aupetit_6_2_15i _)]
    rw [star_mul, star_star, mySesquilinear_apply]
  add_left a b c := by
    repeat rw [mySesquilinear_apply]
    rw [← map_add]
    congr
    #check norm a
    sorry
  smul_left _ _ _ := sorry
-- see https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Proving.20Quotient.20Structures/with/545799315











/-


#check (mySesquilinear f) p
#check preHil
#check (A ⧸ N f)
#check Quotient.lift (mySesquilinear f)

theorem helper (b : A) :  N f ≤ LinearMap.ker ((mySesquilinear f) b) := by
  intro a ainNf
  rw [LinearMap.mem_ker, mySesquilinear_apply]
  have faaZero : f (star a * a) = 0 := by exact ainNf
  -- the code chunk below is re-used a lot. Consider refactor
  have hab := aupetit_6_2_15ii f (star b) (star a)
  rw [star_star, star_star] at hab
  rw [faaZero, mul_zero] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

noncomputable
def secondHalf := Submodule.liftQ (N f) ((mySesquilinear f) p) ((helper f) p)
#check secondHalf f

noncomputable
def linearSecondHalf : LinearMap (starRingEnd ℂ) A (A ⧸ N f →ₗ[ℂ] ℂ) where
  toFun := (secondHalf f)
  map_add' := by
    intro x y
    dsimp [secondHalf]
    simp only [map_add]
    ext x_1 : 2
    simp_all only [Submodule.liftQ_mkQ, LinearMap.add_apply,
      mySesquilinear_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
  map_smul' := by
    intro c x
    dsimp [secondHalf]
    simp only [LinearMap.map_smulₛₗ]
    ext x_1 : 2
    simp_all only [Submodule.liftQ_mkQ, LinearMap.smul_apply,
      mySesquilinear_apply, smul_eq_mul, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply] -- was aesop

theorem helper2 : N f ≤ LinearMap.ker (linearSecondHalf f) := by
  intro a ainNf
  rw [LinearMap.mem_ker]
  dsimp [linearSecondHalf, secondHalf]
  ext b
  have faaZero : f (star a * a) = 0 := by exact ainNf
  have hab := aupetit_6_2_15ii f (star a) (star b)
  rw [star_star, star_star] at hab
  rw [faaZero, zero_mul] at hab
  norm_cast at hab
  rw [sq_nonpos_iff, norm_eq_zero] at hab
  simp_all only [Submodule.liftQ_mkQ, mySesquilinear_apply,
    LinearMap.zero_comp, LinearMap.zero_apply] -- was aesop


noncomputable
def myLiftedSequiLinar := Submodule.liftQ (N f) (linearSecondHalf f) (helper2 f)
#check myLiftedSequiLinar f

--theorem aupetit6_2_18_closed : IsClosed {a : A | f (star a * a) = 0} := by sorry
variable (f : A →ₚ[ℂ] ℂ)
#check N f
#check Ideal.coe_closure (N f)
#check (N f).closure
#check ((N f) : Set A)

theorem aupetit6_2_18_closed' : (N f) = (N f).closure := by sorry

theorem aupetit6_2_18_closed : IsClosed ((N f) : Set A) := by sorry

variable (x : A)
#check x * star x
#check spectralRadius ℂ (x * star x)
#check (spectralRadius ℂ (x * star x)).toReal
#check IsSelfAdjoint.spectralRadius_eq_nnnorm
#check IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm

-- Notation: ρ is spectral radius!!
theorem aupetit_6_2_15iiib (x : A) :
  f (1 : A) * f (x * star x) ≤ ((f (1 : A)) ^ 2) * (spectralRadius ℂ (x * star x)).toReal := by
  sorry

-- theorem aupetit_6_2_15iiic (x : A) : norm (f x) ≤ f (1 : A) * norm x  := by sorry


-- theorem aupetit_6_2_15iiid : norm (f) = f (1 : A)  := by sorry

-- Begin code from Eric Wieser
-- noncomputability should be fixed in by Eric Wieser's bug fix
noncomputable def mySesquilinear (f : A →ₚ[ℂ] ℂ) : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ A).comp (starLinearEquiv ℂ (A := A) : A →ₗ⋆[ℂ] A) |>.compr₂ₛₗ f

@[simp]
theorem mySesquilinear_apply (f : A →ₚ[ℂ] ℂ) (x y : A) :
  mySesquilinear f x y = f (star x * y) := rfl
-- End code from Eric Wieser

-/
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
