import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Data.Real.StarOrdered

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)
variable (p : A) (q : A)

theorem aupetit_6_2_15ii (x y : A) :
  norm (f (x * star y)) ^ 2 ≤ f (x * star x) * f (y * star y) := by sorry

def N (f : A →ₚ[ℂ] ℂ) : Submodule ℂ A where
  carrier := {a : A | f (star a * a) = 0}
  add_mem' := sorry
  zero_mem' := by simp;
  smul_mem' := sorry

-- Begin code from Eric Wieser
noncomputable def mySesquilinear (f : A →ₚ[ℂ] ℂ) : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ A).comp (starLinearEquiv ℂ (A := A) : A →ₗ⋆[ℂ] A) |>.compr₂ₛₗ f

@[simp]
theorem mySesquilinear_apply (f : A →ₚ[ℂ] ℂ) (x y : A) :
  mySesquilinear f x y = f (star x * y) := rfl
-- End code from Eric Wieser

noncomputable instance myInnerProductSpace : InnerProductSpace.Core ℂ (A ⧸ N f) where
  inner a b := mySesquilinear f (Quotient.out a) (Quotient.out b)
  re_inner_nonneg := by
    intro a
    rw [mySesquilinear_apply, RCLike.re_to_complex]

    sorry
  definite := by
    intro a h
    dsimp [myLiftedSesquiLinear] at h
    dsimp [linearSecondHalf] at h
  conj_inner_symm := by
    intro a b
    sorry
  add_left _ _ _ := LinearMap.map_add₂ _ _ _ _
  smul_left _ _ _ := sorry_
