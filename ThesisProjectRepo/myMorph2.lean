import ThesisProjectRepo.myQuot
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Mul

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder
variable (f : A →ₚ[ℂ] ℂ)


open GNS

/-
1. Define multiplication A→A→A
- prove linear
- prove continuous
2. Define multiplication (A f)→(A f)→(A f)
-/


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

noncomputable
def myQuotToMyQuotLin (a : WithFunctional A f) : (myQuot f) →ₗ[ℂ] (myQuot f) where
  toFun := Submodule.mapQ (GNS.N f) (GNS.N f) (AWithToAWithLin f a) (helper f a)
  map_add' := by simp
  map_smul' := by simp
-- linear, but not continuous
-- prove continuity by bound
theorem bound (a : A) : (∀ (x : myQuot f), ‖(myQuotToMyQuotLin f a) x‖ ≤ 1 * ‖x‖) := by
  intro x
  have h := aupetit_6_2_15iiia f
  -- we want to have f(x^*x)≤ f(1)∣x∣^2
  -- I think this requires using the definition of the norm, then the inner product
  -- work it out on a whiteboard
  sorry

variable (a : A)
#check bound f a
#check LinearMap.mkContinuous (myQuotToMyQuotLin f a) 1 (bound f a)-- linear map and a bound gives a coutinous linear map


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
