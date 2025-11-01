import ThesisProjectRepo.myQuot
import Mathlib.Analysis.VonNeumannAlgebra.Basic

import Mathlib.Analysis.InnerProductSpace.Adjoint

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder
variable (f : A →ₚ[ℂ] ℂ)

open GNS

#check GNS.H f
#check H f
#check GNS.HilbertSpaceFromFunctional f

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

--def T (a : A) (b : Quotient.mk c) := sorry

-- send the element of A to H f, then multiply in H f

def basicMulOnA := @HMul.hMul A A A instHMul
def basicMul :=
  @HMul.hMul (WithFunctional A f) (WithFunctional A f) (WithFunctional A f) instHMul

#check basicMulOnA
#check basicMul f

def halfLinearMul (a : WithFunctional A f) :
  (WithFunctional A f) →ₗ[ℂ] (WithFunctional A f) where
  toFun b := basicMul f a b
  map_add' x y := by simp [basicMul, mul_add]
  map_smul' x y := by simp [basicMul]

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

def halfLinearMulAByQuotToQuot (a : WithFunctional A f) :
  (myQuot f) →ₗ[ℂ] (myQuot f) where
  toFun := Submodule.mapQ (GNS.N f) (GNS.N f) (halfLinearMul f a) (helper f a)
  map_add' := by simp
  map_smul' := by simp

#check halfLinearMulAByQuotToQuot f

def TWithFunctional : (WithFunctional A f) →ₗ[ℂ] (myQuot f) →ₗ[ℂ] myQuot f where
  toFun := halfLinearMulAByQuotToQuot f
  map_add' x y := by
    ext c
    induction c using Submodule.Quotient.induction_on with | _ c
    · simp [halfLinearMulAByQuotToQuot, halfLinearMul, basicMul]
      rw [add_mul]
      rfl
  map_smul' c y := by
    ext c
    induction c using Submodule.Quotient.induction_on with | _ c
    · simp [halfLinearMulAByQuotToQuot, halfLinearMul, basicMul]

def TOnQuot : A →ₗ[ℂ] (myQuot f) →ₗ[ℂ] myQuot f := TWithFunctional f

noncomputable
def T (a : A) : H f → H f := UniformSpace.Completion.map (TWithFunctional f a)
#check T f

-- Raise T to make an HMul on H f

#check BH f

--instance (a : A) : H f →+* H f where

--instance (a : A) : ContinuousLinearMap (T f a) where

instance (a : A) :((H f) →L[ℂ] (H f)) where
  toFun := T f a
  map_add' x y := by
    simp [T, TWithFunctional, halfLinearMulAByQuotToQuot]
    have : halfLinearMul f a = basicMul f a := by rfl
    have : (GNS.N f).mapQ (GNS.N f) (halfLinearMul f a) = (GNS.N f).mapQ (GNS.N f) (basicMul f a) := by rfl
    norm_cast


  map_smul' := sorry


-- lift to H f first, then the completion


#check TWithFunctional f
#check TOnQuot f
