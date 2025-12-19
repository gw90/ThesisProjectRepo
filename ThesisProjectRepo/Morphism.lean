import Mathlib.Analysis.InnerProductSpace.Adjoint
import ThesisProjectRepo.Construction

open ComplexConjugate
open scoped ComplexOrder
open Complex

open UniformSpace
open SeparationQuotient
open UniformSpace.Completion

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

open GNS

noncomputable
instance AWithToAWithLin (a : WithFunctional A f) : WithFunctional A f →ₗ[ℂ] WithFunctional A f
  := (ContinuousLinearMap.mul ℂ (WithFunctional A f)) a

-- I golfed this so much that it's basically unreadable now.
-- Refer to commit from before december 17 for better
theorem helper (a : WithFunctional A f) :
  GNS.N f ≤ Submodule.comap (AWithToAWithLin f a) (GNS.N f) := by
  intro x xh
  have hab := CS_with_functional f ((star a) * (a * x)) x
  rw [star_mul, star_star, xh, mul_zero] at hab
  norm_cast at hab
  apply (_root_.sq_nonpos_iff ‖f (star (a * x) * a * x)‖).mp at hab
  rwa [norm_eq_zero, mul_assoc] at hab

-- define the helper positive linear functional g
-- this is excessively golfed as of December 17 too
def g (b : A) : A →ₚ[ℂ] ℂ where
  toFun x := f (star b * x * b)
  map_add' x y := by
    rw [mul_add, add_mul, map_add]
  map_smul' m x := by simp
  monotone' := by
    unfold Monotone
    intro y z hyz
    apply le_neg_add_iff_le.mp
    obtain ⟨q, hq⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg_of_le hyz)
    rw [add_comm, ← sub_eq_add_neg, ← map_sub, mul_assoc, mul_assoc,
      ← mul_sub (star b) (z * b) (y * b), ← sub_mul, ← mul_assoc,
      hq, ← mul_assoc, mul_assoc (star b * star q), ← star_mul]
    exact PositiveLinearMap.map_nonneg f (star_mul_self_nonneg (q * b))

@[simp]
lemma g_apply (b : WithFunctional A f) (x : WithFunctional A f) :
  f (star b * x * b) = (g f b) x := by rfl

variable (a : WithFunctional A f)

noncomputable
def π_OfA_onQuot : (myQuot f) →ₗ[ℂ] (myQuot f) where
  toFun := Submodule.mapQ (GNS.N f) (GNS.N f) (AWithToAWithLin f a) (helper f a)
  map_add' := by simp
  map_smul' := by simp

lemma πa_OfA_onQuot_apply (b : WithFunctional A f) :
  (π_OfA_onQuot f a) (Submodule.Quotient.mk b) = Submodule.Quotient.mk (a * b) := by rfl

lemma boundedUnitBall :
  (∀ z ∈ Metric.ball 0 1, ‖(π_OfA_onQuot f a) z‖ ≤ ‖a‖) := by
  intro b bh
  rw [Metric.mem_ball, dist_zero_right,
    show ‖b‖ = √(RCLike.re ((myInnerProductSpace f).inner b b)) from rfl] at bh
  induction b using Submodule.Quotient.induction_on with | _ b
  rw [inner_f_apply_on_quot_mk, RCLike.re_to_complex] at bh
  have bh' : √(f (star b * b)).re ≤ 1 := by linarith
  have prodInR := f_of_x_star_x_is_real f (star b)
  have staraaPos := (mul_star_self_nonneg (star a : A))
  have starbPos := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg (star b : A))
  rw [star_star, πa_OfA_onQuot_apply] at *
  have bh2 : (f (star b * b)).re ≤ 1 := (Real.sqrt_le_one (x := (f (star b * b)).re)).mp bh'
  have hyp1 : f (star b * b) ≤ 1 := by rw [← prodInR]; norm_cast
  change ‖aToMyQuot f (a * b)‖ ≤ ‖a‖
  rw [show
      ‖aToMyQuot f (a * b)‖ =
        √(RCLike.re ((myInnerProductSpace f).inner
          (Submodule.Quotient.mk (a * b)) (Submodule.Quotient.mk (a * b))))
      from rfl,
    inner_f_apply_on_quot_mk, star_mul, RCLike.re_to_complex, ← mul_assoc]
  nth_rw 2 [mul_assoc]
  rw [g_apply]
  have : (g f b) 1 = f (star b * b) := by simp [← g_apply f b 1]
  have gval_real : ((g f b) (star a * a)).re = ((g f b) (star a * a)) := by
    have := f_of_x_star_x_is_real (g f b) (star a); rwa [star_star] at this
  have gval_pos : 0 ≤ ((g f b) (star a * a)).re := by
    have := PositiveLinearMap.map_nonneg (g f b) (mul_star_self_nonneg (star a : A))
    rw [star_star, ← gval_real] at this
    simpa
  have step2 := PositiveLinearMap.norm_apply_le_of_nonneg (g f b) (star a * a) staraaPos
  rw [this, ← gval_real, norm_real, Real.norm_eq_abs, abs_of_nonneg gval_pos] at step2
  have step3 : ‖f (star b * b)‖ * ‖star a * a‖ ≤ 1 * ‖star a * a‖ := by
    nlinarith [norm_nonneg (star a * a), norm_nonneg (f (star b * b)),
      (CStarAlgebra.norm_le_one_iff_of_nonneg (f (star b * b)) starbPos).mpr hyp1]
  norm_num at step3
  nth_rw 2 [CStarRing.norm_star_mul_self] at step3
  rw [← pow_two] at step3
  have step4 : ((g f b) (star a * a)).re ≤ ‖a‖ ^ 2 := by linarith
  exact (Real.sqrt_le_left (norm_nonneg a)).mpr step4

lemma bound_on_π_exists :
  ∃ C, ∀ (z : myQuot f), ‖(π_OfA_onQuot f a) z‖ ≤ C * ‖z‖ :=
  LinearMap.bound_of_ball_bound
    (r := 1) (Real.zero_lt_one) (norm a) (π_OfA_onQuot f a) (boundedUnitBall f a)

-- maybe later try to make a specific bound so that it can be computable
noncomputable
def π_onQuot : (myQuot f) →L[ℂ] (myQuot f) :=
  LinearMap.mkContinuousOfExistsBound (π_OfA_onQuot f a) (bound_on_π_exists f a)

lemma π_nonCont_eq_π :
  (π_onQuot f a) = (π_OfA_onQuot f a) := by dsimp [π_onQuot]

lemma π_nonCont_eq_π_on_input (b : myQuot f) :
  (π_onQuot f a) b = (π_OfA_onQuot f a) b := by dsimp [π_onQuot]

@[simp]
lemma π_apply_on_quot (b : WithFunctional A f) :
  ((π_onQuot f a) (Submodule.Quotient.mk b)) = Submodule.Quotient.mk (a * b) := by
    rw [π_nonCont_eq_π_on_input f a (Submodule.Quotient.mk b), πa_OfA_onQuot_apply]

lemma π_onCompletion_onQuot_equiv (b : myQuot f) :
  Completion.map ⇑(π_onQuot f a) ↑b = (π_onQuot f a) b := by
    simp [map_coe (ContinuousLinearMap.uniformContinuous (π_onQuot f a))]

noncomputable
def π_OfA (a : WithFunctional A f) : H f →L[ℂ] H f where
  toFun := UniformSpace.Completion.map (π_onQuot f a)
  map_add' x y := by
    induction x using induction_on with
    | hp => exact (isClosed_eq ((continuous_map).comp (by continuity))
        (Continuous.add (continuous_map) (continuous_const)))
    | ih x
    induction y using induction_on with
    | hp => exact (isClosed_eq ((continuous_map).comp (by continuity))
        (Continuous.add (continuous_const) (continuous_map)))
    | ih y
    rw [← coe_add]
    simp only [π_onCompletion_onQuot_equiv, map_add]
    rw [coe_add]
  map_smul' x y := by
    induction y using induction_on with
    | hp => exact (isClosed_eq ((continuous_map).comp (continuous_const_smul x))
        (Continuous.smul (continuous_const) (continuous_map)))
    | ih y
    rw [← Completion.coe_smul, π_onCompletion_onQuot_equiv]
    simp[π_onCompletion_onQuot_equiv]
  cont := continuous_map

open ContinuousLinearMap

noncomputable
def π : StarAlgHom ℂ (WithFunctional A f) (H f →L[ℂ] H f) where
  toFun := π_OfA f
  map_one' := by
    ext b
    induction b using induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih b
    induction b using Submodule.Quotient.induction_on
    simp [π_OfA, π_onCompletion_onQuot_equiv]
  map_mul' a b := by
    ext c
    induction c using induction_on with
    | hp => exact (isClosed_eq (by continuity)
          (ContinuousLinearMap.continuous ((π_OfA f (a)).comp (π_OfA f (b)))))
    | ih c
    induction c using Submodule.Quotient.induction_on
    simp [π_OfA, π_onCompletion_onQuot_equiv, ← mul_assoc]
  map_zero' := by
    ext y
    induction y using induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih y
    induction y using Submodule.Quotient.induction_on
    simp [π_OfA, π_onCompletion_onQuot_equiv, π_nonCont_eq_π_on_input, π_OfA_onQuot,
      AWithToAWithLin]
    rfl
  map_add' x y := by
    ext c
    rw [ContinuousLinearMap.add_apply]
    induction c using induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih c
    induction c using Submodule.Quotient.induction_on
    simp [π_OfA, π_onCompletion_onQuot_equiv, π_nonCont_eq_π_on_input, π_OfA_onQuot,
      AWithToAWithLin, Completion.coe_add]
  commutes' r := by
    simp only [← RingHom.smulOneHom_eq_algebraMap, RingHom.smulOneHom_apply, π_OfA]
    congr
    ext c
    simp only [π_onQuot, LinearMap.mkContinuousOfExistsBound_apply]
    induction c using Submodule.Quotient.induction_on
    simp [πa_OfA_onQuot_apply]
  map_star' a := by
    refine (ContinuousLinearMap.eq_adjoint_iff (π_OfA f (star a)) (π_OfA f a)).mpr ?_
    intro x y
    induction x using induction_on with
    | hp => exact (isClosed_eq (by continuity)
      (Continuous.inner (continuous_id) (continuous_const)))
    | ih x
    induction y using induction_on with
    | hp => exact (isClosed_eq (Continuous.inner (continuous_const) (continuous_id))
        (Continuous.inner (by continuity) (by continuity)))
    | ih y
    induction x using Submodule.Quotient.induction_on
    induction y using Submodule.Quotient.induction_on
    have (a b : myQuot f) : inner ℂ (coe' a) (coe' b) = inner_f f a b := by rw [inner_coe]; rfl
    simp [π_OfA, π_onCompletion_onQuot_equiv, this, mul_assoc]
