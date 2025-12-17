import ThesisProjectRepo.myQuot
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.Continuous
import Mathlib.Topology.Algebra.Monoid.Defs

open ComplexConjugate
open scoped ComplexOrder
open Complex

open UniformSpace
open SeparationQuotient
open UniformSpace.Completion

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

variable (a : WithFunctional A f)

noncomputable
def π_nonCont : (myQuot f) →ₗ[ℂ] (myQuot f) where
  toFun := Submodule.mapQ (GNS.N f) (GNS.N f) (AWithToAWithLin f a) (helper f a)
  map_add' := by simp
  map_smul' := by simp

lemma πa_apply (b : WithFunctional A f) :
  (π_nonCont f a) (Submodule.Quotient.mk b) = Submodule.Quotient.mk (a * b) := by rfl

lemma boundedUnitBall :
  (∀ z ∈ Metric.ball 0 1, ‖(π_nonCont f a) z‖ ≤ ‖a‖) := by
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
        √(RCLike.re ((myInnerProductSpace f).inner
          (Submodule.Quotient.mk (a * b)) (Submodule.Quotient.mk (a * b))))
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

lemma bound_on_π_exists :
  ∃ C, ∀ (z : myQuot f), ‖(π_nonCont f a) z‖ ≤ C * ‖z‖ :=
  LinearMap.bound_of_ball_bound
    (r := 1) (Real.zero_lt_one) (norm a) (π_nonCont f a) (boundedUnitBall f a)

-- maybe later try to make a specific bound so that it can be computable
noncomputable
def π_onQuot : (myQuot f) →L[ℂ] (myQuot f) :=
  LinearMap.mkContinuousOfExistsBound (π_nonCont f a) (bound_on_π_exists f a)

lemma π_nonCont_eq_π :
  (π_onQuot f a) = (π_nonCont f a) := by dsimp [π_onQuot]

lemma π_nonCont_eq_π_on_input (b : myQuot f) :
  (π_onQuot f a) b = (π_nonCont f a) b := by dsimp [π_onQuot]

@[simp]
lemma π_apply_on_quot (b : WithFunctional A f) :
  ((π_onQuot f a) (Submodule.Quotient.mk b)) = Submodule.Quotient.mk (a * b) := by
    rw [π_nonCont_eq_π_on_input f a (Submodule.Quotient.mk b), πa_apply]

lemma π_onCompletion_onQuot_equiv (b : myQuot f) :
  Completion.map ⇑(π_onQuot f a) ↑b = (π_onQuot f a) b := by
    simp [map_coe (ContinuousLinearMap.uniformContinuous (π_onQuot f a))]

/-
Steps:
1. Extend π f a to a continuous function on H f
2. Prove that it is still linear
   Use fact of agreeing on dense set, combined with continuity
3. Prove π (not π(a)) is also linear
3. Prove multiplicativity
4. Prove *-preserving
-/

/-
To-dos:
1. figure out how to deal with the completion thing
   i.e. how to consider a representative from myQuot f
-/

#check H f
#check UniformSpace.Completion.induction_on

--agreement of continuous functions on myQuot f implies equality on H f
#check UniformSpace.Completion.ext
-- same as above, but you specify space explicitly
#check UniformSpace.Completion.ext'
-- if two functions are equal regardless of wether you move them to the completion
-- before or after applying the function, then they are equal
-- probably not useful
#check UniformSpace.Completion.map_unique

--Extend a linear equivalence between normed spaces to a continuous linear equivalence
-- between Banach spaces with two dense maps e₁ and e₂ and the corresponding norm estimates.
-- #check LinearEquiv.extend
-- I might not have a LinearEquiv

noncomputable
def π_LinContWithA (a : WithFunctional A f) : H f →L[ℂ] H f where
  toFun := UniformSpace.Completion.map (π_onQuot f a)
  map_add' x y := by
    refine induction_on x
      (isClosed_eq ((continuous_map (f := π_onQuot f a)).comp
        (Continuous.add (continuous_id) (continuous_const (y := y))))
        (continuous_id.comp (Continuous.add (continuous_map (f := π_onQuot f a))
          (continuous_const (y := Completion.map (⇑(π_onQuot f a)) y)))))
      ?_
    intro b
    refine induction_on y
      (isClosed_eq ((continuous_map (f := π_onQuot f a)).comp
        (Continuous.add (continuous_const (y := coe' b)) (continuous_id)))
        (continuous_id.comp (Continuous.add
          (continuous_const (y := Completion.map (⇑(π_onQuot f a)) ↑b))
          (continuous_map (f := (⇑(π_onQuot f a)))))))
      ?_
    intro c
    have : (b : Completion (myQuot f)) + ↑c = ↑(b + c) := by exact Eq.symm (coe_add b c)
    rw [this]
    simp [π_onCompletion_onQuot_equiv]
    rw [coe_add]
  map_smul' x y := by
    simp
    refine induction_on y
      (isClosed_eq ((continuous_map (f := π_onQuot f a)).comp
        (continuous_const_smul x))
        (continuous_id.comp (Continuous.smul
          (continuous_const (y := x))
          (continuous_map (f := (⇑(π_onQuot f a)))))))
      ?_
    intro c
    have : (x • (c : Completion (myQuot f))) = ↑(x • c) := Eq.symm (Completion.coe_smul x c)
    rw [this]
    rw [π_onCompletion_onQuot_equiv]
    simp[π_onCompletion_onQuot_equiv]
  cont := UniformSpace.Completion.continuous_map (f := (π_onQuot f a))

variable [CStarAlgebra (H f →L[ℂ] H f)] -- maybe this does what I want?
-- from here, follow Aguilar p. 253
noncomputable
def π : A →L[ℂ] (H f →L[ℂ] H f) where
  toFun := π_LinContWithA f
  map_add' x y := by
    ext c
    rw [ContinuousLinearMap.add_apply]
    refine induction_on c
      (isClosed_eq (ContinuousLinearMap.continuous (f := π_LinContWithA f (x+y)))
        (continuous_id.comp (
          Continuous.add
            (ContinuousLinearMap.continuous (π_LinContWithA f x))
            (ContinuousLinearMap.continuous (π_LinContWithA f y)))))
      ?_
    intro b
    dsimp [π_LinContWithA]
    simp [π_onCompletion_onQuot_equiv, π_nonCont_eq_π_on_input]
    dsimp [π_nonCont]
    dsimp [AWithToAWithLin]
    induction b using Submodule.Quotient.induction_on with | _ b
    simp only [Submodule.mapQ_apply, ContinuousLinearMap.coe_coe]
    dsimp [AWithToAWithLinCont]
    rw [← coe_add, ← Submodule.Quotient.mk_add, ← add_mul]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    ext y
    refine induction_on y
      (isClosed_eq ((ContinuousLinearMap.continuous (π_LinContWithA f (c • x))))
        (continuous_id.comp (Continuous.smul
          (continuous_const (y := c))
          (ContinuousLinearMap.continuous (π_LinContWithA f x)))))
      ?_
    intro b
    dsimp [π_LinContWithA]
    simp [π_onCompletion_onQuot_equiv, π_nonCont_eq_π_on_input]
    dsimp [π_nonCont]
    dsimp [AWithToAWithLin]
    induction b using Submodule.Quotient.induction_on with | _ b
    simp only [Submodule.mapQ_apply, ContinuousLinearMap.coe_coe]
    dsimp [AWithToAWithLinCont]
    simp only [Algebra.smul_mul_assoc, Submodule.Quotient.mk_smul, Completion.coe_smul]
  cont := by
    -- prove bounded?
    -- Aupetit states that the bounding constant should be 1
    
    sorry

-- I think I probably need to specify some more structure on H f →L[ℂ] H f
lemma π_unital : π f (1 : A) = (1 : H f →L[ℂ] H f) := by
  ext b
  rw [ContinuousLinearMap.one_apply] -- 1 is definitely the identity
  sorry

lemma π_mult (a b : WithFunctional A f) : π f (a * b) = (π f a) * (π f b) := by
  sorry

-- how do I know that the below statemnt is using the correct adjoint in B(H_f)?
lemma π_star_preserving (a : WithFunctional A f) : π f (star a) = star (π f a) := by
  sorry

noncomputable
instance : StarAlgHom ℂ (WithFunctional A f) (H f →L[ℂ] H f) where
  toFun := π f
  map_one' := π_unital f
  map_mul' := π_mult f
  map_zero' := ContinuousLinearMap.map_zero (π f)
  map_add' := ContinuousLinearMap.map_add (π f)
  commutes' r := sorry
  map_star' := π_star_preserving f
