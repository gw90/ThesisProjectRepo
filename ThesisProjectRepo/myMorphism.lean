import ThesisProjectRepo.myQuot
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Adjoint
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder
variable (f : A →ₚ[ℂ] ℂ)

open GNS

def BH := (H f) →L[ℂ] (H f)

open ContinuousLinearMap

noncomputable instance : Star (BH f) := by unfold BH; infer_instance

noncomputable instance : InvolutiveStar (BH f) := by unfold BH; infer_instance

noncomputable instance : NonUnitalNonAssocSemiring (BH f) := by unfold BH; infer_instance

noncomputable instance : StarRing (BH f) := by unfold BH; infer_instance

noncomputable instance : SMul ℂ (BH f) := by unfold BH; infer_instance

-- represents a Star Algebra because we also have [Algebra R A]
noncomputable instance : StarModule ℂ (BH f) := by unfold BH; infer_instance

noncomputable instance : Semiring (BH f) := by unfold BH; infer_instance

noncomputable instance : Algebra ℂ (BH f) := by unfold BH; infer_instance

#check StarSubalgebra ℂ (BH f) -- this typechecks because it is true

instance : HMul (A) (A) (A) := by infer_instance
instance : HMul (WithFunctional A f) (WithFunctional A f) (WithFunctional A f) := by infer_instance

def basicMulOnA := @HMul.hMul A A A instHMul
def basicMul :=
  @HMul.hMul (WithFunctional A f) (WithFunctional A f) (WithFunctional A f) instHMul

#check basicMulOnA
#check basicMul f

instance : TopologicalSpace (WithFunctional A f) := by infer_instance

def halfLinearMul (a : WithFunctional A f) : (WithFunctional A f) →ₗ[ℂ] (WithFunctional A f) where
  toFun b := basicMul f a b
  map_add' x y := by simp [basicMul, mul_add]
  map_smul' x y := by simp [basicMul]

@[simp]
theorem halfLinearMulEquivBasicMul (a : A) : halfLinearMul f a = basicMul f a := by rfl

#check halfLinearMul f

theorem helper (a : WithFunctional A f) :
  GNS.N f ≤ Submodule.comap (halfLinearMul f a) (GNS.N f) := by
  intro x xh
  simp [halfLinearMul, basicMul]
  have fxx : f (star x * x) = 0 := xh
  change f (star (a * x) * (a * x)) = 0
  simp
  have hab := aup_6_2_15ii f (star (a*x) * a) (star x)
  simp [fxx] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero, mul_assoc] at hab

def halfLinearMulAByQuotToQuot (a : WithFunctional A f) : (myQuot f) →ₗ[ℂ] (myQuot f) where
  toFun := Submodule.mapQ (GNS.N f) (GNS.N f) (halfLinearMul f a) (helper f a)
  map_add' := by simp
  map_smul' := by simp

instance halfLinearContMulAByQuotToQuot (a : WithFunctional A f) : (myQuot f) →ₗ[ℂ] (myQuot f) where
  toFun := halfLinearMulAByQuotToQuot f a
  map_add' := by simp
  map_smul' := by simp

variable (a : A)
-- Deal with this nonsense later. Just start writing
--#check ContinuousLinearMap.extend (halfLinearMulAByQuotToQuot f a)

/-
noncomputable
instance AMyQuotMul : HMul A (myQuot f) (myQuot f) where
  hMul a := halfLinearMulAByQuotToQuot f a

def TWithFunctional : (WithFunctional A f) →ₗ[ℂ] (myQuot f) →ₗ[ℂ] myQuot f where
  toFun := halfLinearMulAByQuotToQuot f
  map_add' x y := by
    ext c
    induction c using Submodule.Quotient.induction_on with | _ c
    · simp [halfLinearMulAByQuotToQuot, halfLinearMul, basicMul]
      rw [add_mul]
      rfl
  map_smul' c y := by
    ext d
    induction d using Submodule.Quotient.induction_on with | _ d
    · simp [halfLinearMulAByQuotToQuot, halfLinearMul, basicMul]

def TOnQuot : A →ₗ[ℂ] (myQuot f) →ₗ[ℂ] myQuot f := TWithFunctional f
-/

-- is own completion UniformSpace.Completion.UniformCompletion.completeEquivSelf

open UniformSpace

noncomputable
instance T (a : A) : H f →ₗ[ℂ] H f where
  toFun := Completion.map (halfLinearMulAByQuotToQuot f a)
  map_add' := by sorry
  map_smul' b c := by sorry


noncomputable
instance AHMul : HMul A (H f) (H f) where
  hMul := T f

variable (a : A) (b : H f)
--#check Completion.map_coe (helper2 f a) b
--def helper3coe (a : A) := Completion.map_coe (helper2 f a)

noncomputable
def THalfLinear (a : A) : (H f) →L[ℂ] (H f) where
  toFun := T f a
  map_add' x y := sorry
  map_smul' := sorry
  cont := UniformSpace.Completion.continuous_map (f := halfLinearMulAByQuotToQuot f a)
-- ContinuousLinearMap.extend

def F : A →L[ℂ] ℂ where
  toFun := f
  map_add' := fun x y ↦ map_add f x y
  map_smul' := fun m x ↦ PositiveLinearMap.map_smul_of_tower f m x

#check F f

#check ContinuousLinearMap.extend (F f)
@[simp]
theorem THalfLinearEquivT (a : A) : THalfLinear f a = T f a := by rfl

#check THalfLinear f
noncomputable def TToBH : A →ₗ[ℂ] ((H f) →L[ℂ] (H f)) where
  toFun := THalfLinear f
  map_add' x y := by
    ext c
    simp [T, halfLinearMulAByQuotToQuot]
    sorry
  map_smul' := sorry
#check TToBH f



-- lift to H f first, then the completion

/-
variable (a : A) (h : H f)

noncomputable
instance ASMul : SMul A (H f) where
  smul := T f

noncomputable
instance AHMul : HMul A (H f) (H f) where
  hMul := T f

#check (AHMul f).hMul a

theorem verify : (AHMul f).hMul a = T f a := by rfl

theorem HFComplete :  Completion (H f) = H f := by
    unfold H
    sorry

-- theorem nonAction (a : A) : Completion.extension (T f a) = T f a := by rfl

theorem UniContT (a : A) : UniformContinuous (Completion.extension (T f a)) :=
  Completion.uniformContinuous_extension (f := T f a)

#check Completion.uniformContinuous_extension (f := TWithFunctional f a)

#check UniContT f a
#check Completion.map_coe (UniContT f a) h
#check Completion.map_unique (UniContT f a)
-- instance : Module A (H f) := sorry


#check a * h -- : H f --- good
-- Raise T to make an HMul on H f

#check BH f
#check TOnQuot f a
--instance (a : A) : H f →+* H f where

--instance (a : A) : ContinuousLinearMap (T f a) where
-/


#check TWithFunctional f
#check TOnQuot f
