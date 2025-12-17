import ThesisProjectRepo.myQuot
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Mul

open ComplexConjugate
open scoped ComplexOrder
open Complex

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

open GNS

-- step 1 : A → A
noncomputable instance AtoALinCont (a : A) : A →L[ℂ] A
  := (ContinuousLinearMap.mul ℂ A) a
-- this is linear and continuous

-- step 2 : WithFunctional A f → WithFunctional A f
noncomputable
instance AWithToAWithLinCont (a : WithFunctional A f) : WithFunctional A f →L[ℂ] WithFunctional A f
  := (ContinuousLinearMap.mul ℂ (WithFunctional A f)) a
-- this is linear and continuous
noncomputable
instance AWithToAWithLin (a : WithFunctional A f) : WithFunctional A f →ₗ[ℂ] WithFunctional A f
  := AWithToAWithLinCont f a
-- this is the same, but not continuous

-- step 3 : WithFunctional A f → myQuot f
noncomputable
instance AWithToMyQuotLin (a : WithFunctional A f) : WithFunctional A f →ₗ[ℂ] myQuot f where
  toFun b := aToMyQuot f (((ContinuousLinearMap.mul ℂ (WithFunctional A f)) a) b)
  map_add' c d := by unfold aToMyQuot; rw [ContinuousLinearMap.mul_apply', mul_add]; simp
  map_smul' c d := by unfold aToMyQuot; simp
-- only linear, not continuous
-- so try getting a bound?

-- step 4 : myQuot f → myQuot f
-- does not depend on step 3
theorem helper (a : WithFunctional A f) :
  GNS.N f ≤ Submodule.comap (AWithToAWithLinCont f a) (GNS.N f) := by
  intro x xh
  simp
  have fxx : f (star x * x) = 0 := xh
  change f (star (a * x) * (a * x)) = 0
  simp
  have hab := aup_6_2_15ii f (star (a*x) * a) (star x)
  simp [fxx] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero, mul_assoc] at hab

-- define the helper positive linear functional g
def g (b : A) : A →ₚ[ℂ] ℂ where
  toFun x := f (star b * x * b)
  map_add' x y := by
    rw [mul_add, add_mul, map_add]
  map_smul' m x := by simp
  monotone' := by
    unfold Monotone
    intro y z hyz
    simp
    apply le_neg_add_iff_le.mp
    have : 0 ≤ z-y := sub_nonneg_of_le hyz
    rw [add_comm, ← sub_eq_add_neg]
    rw [← map_sub, mul_assoc, mul_assoc, ← mul_sub (star b) (z * b) (y * b)]
    rw [← sub_mul, ← mul_assoc]
    have := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp this
    obtain ⟨q, hq⟩ := this
    rw [hq]
    rw [← mul_assoc, mul_assoc (star b * star q)]
    rw [← star_mul]
    have : 0 ≤ star (q * b) * (q * b) := star_mul_self_nonneg (q * b)
    exact PositiveLinearMap.map_nonneg f this

-- this might be unnecessary
instance (b : A) : ContinuousLinearMap (σ := RingHom.id ℂ) (M := A) (M₂ := ℂ) where
  toFun := g f b
  map_add' a c := map_add (g f b) a c
  map_smul' a c := PositiveLinearMap.map_smul_of_tower (g f b) a c


@[simp]
lemma g_apply (b : WithFunctional A f) (x : WithFunctional A f) : f (star b * x * b) = (g f b) x := by rfl

-- Note: PositiveLinearMap.instContinuousLinearMapClassComplexOfLinearMapClassOfOrderHomClass
-- should give continuity of g so we can use operator norm properties

noncomputable
def π (a : WithFunctional A f) : (myQuot f) →ₗ[ℂ] (myQuot f) where
  toFun := Submodule.mapQ (GNS.N f) (GNS.N f) (AWithToAWithLin f a) (helper f a)
  map_add' := by simp
  map_smul' := by simp

variable (a : WithFunctional A f)

@[simp]
lemma πa_apply (b : WithFunctional A f) : (π f a) (Submodule.Quotient.mk b) = Submodule.Quotient.mk (a * b) := by rfl

lemma boundedUnitBall : (∀ z ∈ Metric.ball 0 1, ‖(π f a) z‖ ≤ ‖a‖) := by
  intro b bh
  rw [Metric.mem_ball, dist_zero_right] at bh
  -- This can be cleaned up alot
  rw [show ‖b‖ = √(RCLike.re ((myInnerProductSpace f).inner b b)) from rfl] at bh
  induction b using Submodule.Quotient.induction_on with | _ b
  simp at bh
  have bh' : √(f (star b * b)).re ≤ 1 := by linarith
  have prodInR := fOfxStarxIsReal f (star b)
  simp at prodInR
  have bh2 : (f (star b * b)).re ≤ 1 := (Real.sqrt_le_one (x := (f (star b * b)).re)).mp bh'
  have hyp1 : ((f (star b * b)).re : ℂ) ≤ (1 : ℂ) := by norm_cast
  rw [prodInR] at hyp1
  simp only [πa_apply]
  change ‖aToMyQuot f (a * b)‖ ≤ ‖a‖
  rw [show
      ‖aToMyQuot f (a * b)‖ =
        √(RCLike.re ((myInnerProductSpace f).inner (Submodule.Quotient.mk (a * b)) (Submodule.Quotient.mk (a * b))))
      from rfl]
  simp
  rw [← mul_assoc]
  nth_rw 2 [mul_assoc]
  simp
  have staraaPos := (mul_star_self_nonneg (star a : A))
  rw [star_star] at staraaPos
  have step2 := PositiveLinearMap.norm_apply_le_of_nonneg (g f b) (star a * a) staraaPos
  have : (g f b) 1 = f (star b * b) := by rw [← g_apply f b 1]; simp
  rw [this] at step2
  -- use hyp1 to apply an absolute value on the left
  have starbPos := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg (star b : A))
  rw [star_star] at starbPos
  have gval_real : ((g f b) (star a * a)).re = ((g f b) (star a * a)) := by
    have := fOfxStarxIsReal (g f b) (star a); rw [star_star] at this; assumption
  rw [← gval_real] at step2
  simp at step2
  have gval_pos : 0 ≤ ((g f b) (star a * a)).re := by
    have := PositiveLinearMap.map_nonneg (g f b) (mul_star_self_nonneg (star a : A))
    rw [star_star, ← gval_real] at this
    norm_cast at this
  have gval_eq_abs : ((g f b) (star a * a)).re = |((g f b) (star a * a)).re| :=
    Eq.symm (abs_of_nonneg gval_pos)
  rw [← gval_eq_abs] at step2
  have f_val_abs_le_one : ‖f (star b * b)‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (f (star b * b)) starbPos).mpr hyp1
  -- use f_val_abs_le_one and starbPos
  have f_abs_geq_0 : 0 ≤ ‖f (star b * b)‖ := by exact norm_nonneg (f (star b * b))
  have stara_a_geq_0 : 0 ≤ ‖star a * a‖ := by exact norm_nonneg (star a * a)
  have step3 : ‖f (star b * b)‖ * ‖star a * a‖ ≤ 1 * ‖star a * a‖ := by nlinarith
  norm_num at step3
  nth_rw 2 [CStarRing.norm_star_mul_self] at step3
  rw [← pow_two] at step3
  have step4 : ((g f b) (star a * a)).re ≤ ‖a‖ ^ 2 := by linarith
  have abs_a_pos : 0 ≤ ‖a‖ := by exact norm_nonneg a
  exact (Real.sqrt_le_left abs_a_pos).mpr step4

#check LinearMap.bound_of_ball_bound (r := 1) (Real.zero_lt_one) (norm a) (π f a) (boundedUnitBall f a)



/-

  cont := by
    -- Now, we show that π f (a) is continuous on A/Nf
    -- resume proof later. How do I do this in Lean???
    -- I AM SHOWING BOUNDEDNESS ON THE UNIT BALL WITH THE OPERATOR NORM!!!
    have : ∃ b : (WithFunctional A f), norm (aToMyQuot f b) ≤ 1 := by
      use 0
      unfold aToMyQuot
      simp
    obtain ⟨b, hb⟩ := this
    have :=
      InnerProductSpace.Core.ofReal_normSq_eq_inner_self (aToMyQuot f b) (𝕜 := ℂ) (F := myQuot f)
    have h1 : inner ℂ (aToMyQuot f b) (aToMyQuot f b) = f (star b * b) := rfl
    rw [h1] at this
    have norm_eq_sqrt :=
      InnerProductSpace.Core.norm_eq_sqrt_re_inner (aToMyQuot f b) (𝕜 := ℂ) (F := myQuot f)
    simp at norm_eq_sqrt
    rw [h1] at norm_eq_sqrt
    -- use
    #check LinearMap.bound_of_ball_bound (r := 1) (r_pos := by norm_num)
    -- to get a bound from boundedness on the unit ball
    -- to-do: prove boundedness on unit ball

    -- norm_eq_sqrt is now the first equation on p.252
    -- now we should approach the second equation with the chain of calcs
    -- to-do: imply the boundedness we need from constant bound on unit ball
    #check LinearMap.mkContinuous



    #check PositiveLinearMap.norm_apply_le_of_nonneg
    sorry
-- linear, but not continuous
-- WE MUST prove continuity by bound - all sources agree. DO THIS!!!
-- linear + bounded -> continuous
-- Aguilar invokes theorem similar to PositiveLinearMap.norm_apply_le_of_nonneg
-/



/-

noncomputable
def HtoHCont (a : WithFunctional A f) : (GNS.H f) →L[ℂ] (GNS.H f) where
  toFun := UniformSpace.Completion.map (myQuotToMyQuotLin f a)
  map_add' x y := by
    sorry
  map_smul' := by sorry
  cont := UniformSpace.Completion.continuous_map (f := myQuotToMyQuotLin f a)

variable (a : A)
#check HtoHCont f a
#check UniformSpace.Completion.map ⇑(myQuotToMyQuotLin f a)
#check UniformSpace.Completion.continuous_map (f := myQuotToMyQuotLin f a)
#check ContinuousLinearMap.extend (myQuotToMyQuotLin f a)

-- once continuiuty is proven, can we extend to completion?
/-
instance : PartialOrder (myQuot f) := by unfold myQuot; unfold WithFunctional;

noncomputable
def myQuotToMyQuotLinPos (a : WithFunctional A f) : (myQuot f) →ₚ[ℂ] (myQuot f) where
  toFun := Submodule.mapQ (GNS.N f) (GNS.N f) (AWithToAWithLin f a) (helper f a)
  map_add' := by simp
  map_smul' := by simp
-/
-- positivty will not work
theorem bound (a : A) : (∀ (x : myQuot f), ‖(myQuotToMyQuotLin f a) x‖ ≤ 1 * ‖x‖) := by
  intro x
  have h := aupetit_6_2_15iiia f
  -- we want to have f(x^*x)≤ f(1)∣x∣^2
  -- I think this requires using the definition of the norm, then the inner product
  -- work it out on a whiteboard
  sorry

#check bound f a
#check LinearMap.mkContinuous (myQuotToMyQuotLin f a) 1 (bound f a)-- linear map and a bound gives a coutinous linear map
#check myQuotToMyQuotLin f a
#check PositiveLinearMap.exists_norm_apply_le (myQuotToMyQuotLin f a) -- need to prove positivity, which requires partial order


#check NonUnitalAlgHom.Lmul ℂ A -- this could be exactly what I need
#check ContinuousLinearMap.mulₗᵢ


/-
Alternate method: use NonUnitalAlgHom.Lmul ℂ (myQuot f)
This method might technically be better, but try it later because it is less
similar to what the books do
-/

--#check NonUnitalAlgHom.Lmul ℂ (myQuot f)

/-

-- π_f (a) (b + N_f) = ab + N_f
-- π_f (a) : myQuot → myQuot

-- 1. get a linear map from A to A
-- 2. get a linear map from myQuot to myQuot
-- 3. Prove that that map is continuous
-- 4. Extend it to the completion with ContinuousLinearMap.extend

-- step 1
-- step 4
--#check ContinuousLinearMap.extend (ContQuotToQuotLinContMul f a) (F := GNS.H f) (𝕜 := ℂ)
-- this raises the domain, so we have to raise the codomain first

-- step 1: underlying multiplication is continuous
#check ContinuousLinearMap.mul ℂ A -- gives multiplication over is continuous linear

noncomputable
instance AtoALinContMul (a : A) : A →L[ℂ] A := (ContinuousLinearMap.mul ℂ A) a

variable (a : WithFunctional A f)
#check (ContinuousLinearMap.mul ℂ (WithFunctional A f)) a

noncomputable
def AWithToAWithLinContMul (a : WithFunctional A f) := (ContinuousLinearMap.mul ℂ (WithFunctional A f)) a
#check AWithToAWithLinContMul

--This is dubious: really think about it
--#check ContinuousLinearMap.mul ℂ (GNS.H f)

-- state that the multiplication on the quotient space is continuous linear
-- now we send the continuous linear map to a quotient space. I think I can compose with a continuous linear quotient map
-- alternatively, what's the minimum math I need to get the bound?

-- I think this can be defined, but depends on some stuff that involves the proof that the quotient is well-defined
-- and we need to us the weird quotient induction thing
--noncomputable
--instance : SeminormedRing (myQuot f) where

#check NonUnitalAlgHom.Lmul ℂ A -- this could be exactly what I need
--#check NonUnitalAlgHom.Lmul ℂ (myQuot f) -- this would be almost exactly what I need
#check ContinuousLinearMap.mulₗᵢ

#check UniformSpace.Completion.continuous_map

-- Mathlib.Analysis.Normed.Operator.ContinuousLinearMap has bounded implies continuous
-- useful if following Aupetit

-- maybe all I need to construct is a linear map
#check LinearMap.mkContinuous -- linear map and a bound gives a coutinous linear map
-/
