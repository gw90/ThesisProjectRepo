import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

variable [PartialOrder ℂ]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A]
variable (f : A →ₚ[ℂ] ℂ)

def WithFunctional (_A : Type*) [CStarAlgebra _A] [PartialOrder _A] (_f : _A →ₚ[ℂ] ℂ) := _A

namespace WithFunctional

/-- The canonical inclusion of `A` into `WithFunctional A f`. -/
def toFunctional : A → WithFunctional A f := id

/-- The canonical inclusion of `WithFunctional A f` into `A`. -/
def ofFunctional : WithFunctional A f → A := id

/-- `WithFunctional.toFunctional` and `WithFunctional.toFunctional` as an equivalence. -/
@[simps]
protected def equiv : WithFunctional A f ≃ A where
  toFun := ofFunctional f
  invFun := toFunctional f
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup [AddCommGroup A] : AddCommGroup (WithFunctional A f) := ‹AddCommGroup A›
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring A] :
  NonUnitalNonAssocSemiring (WithFunctional A f) := ‹NonUnitalNonAssocSemiring A›
instance instModule [Semiring ℂ] [AddCommGroup A] [Module ℂ A] :
  Module ℂ (WithFunctional A f) := ‹Module ℂ (WithFunctional A f)›

/-
-- Some other properties I could specify:
instance instStarAddMonoid [StarAddMonoid A] : StarAddMonoid (WithFunctional A f) :=
 ‹StarAddMonoid A›
instance instAddCommMonoid [AddCommMonoid (StarAddMonoid A)] :
  AddCommMonoid (StarAddMonoid (WithFunctional A f)) :=
 ‹AddCommMonoid (StarAddMonoid A)›
 variable [PartialOrder (WithFunctional A f)]
instance instStarAddMonoidFunctional [StarAddMonoid (A →ₗ⋆[ℂ] A)] :
  StarAddMonoid (WithFunctional A f →ₗ⋆[ℂ] WithFunctional A f) :=
  ‹StarAddMonoid (A →ₗ⋆[ℂ] A)›
-/

def myInner (a b : WithFunctional A f) : ℂ := f (star b * a)
#check myInner f

instance myInnerProductSpace : PreInnerProductSpace.Core ℂ (WithFunctional A f) where
  inner := myInner f
  re_inner_nonneg := sorry
  conj_inner_symm := sorry
  add_left := sorry
  smul_left := sorry

example (a b : WithFunctional A f) :
  norm (f (a * star b)) ^ 2 ≤ (f (a * star a)).re * (f (b * star b)).re := by
  have cs := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) (x := a) (y := b)
  have : (myInnerProductSpace f).inner = myInner f := by rfl
  rw [this] at cs
  dsimp [myInner] at cs
  -- have to show that the conjugate is still the same
  sorry



end WithFunctional


/-

/-noncomputable def mySesquilinear :
  (WithFunctional f A) →ₗ⋆[ℂ] (WithFunctional f A) →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ (WithFunctional f A)).comp (starLinearEquiv ℂ (WithFunctional f A) :
    (WithFunctional f A) →ₗ⋆[ℂ] (WithFunctional f A)) |>.compr₂ₛₗ f-/

noncomputable def mySesquilinear (p : WithFunctional f A) :
  (WithFunctional f A) →ₗ⋆[ℂ] (WithFunctional f A) →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ (WithFunctional f A)).comp (starLinearEquiv ℂ (WithFunctional f A) :
    (WithFunctional f A) →ₗ⋆[ℂ] (WithFunctional f A)) |>.compr₂ₛₗ f

@[simp]
theorem mySesquilinear_apply (x y : (WithFunctional f A)) :
  mySesquilinear f x y = f (star x * y) := rfl
-/
/- Begin code from Eric Wieser
noncomputable def mySesquilinear (f : (WithFunctional f A) →ₚ[ℂ] ℂ) :
  (WithFunctional f A) →ₗ⋆[ℂ] (WithFunctional f A) →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ (WithFunctional f A)).comp (starLinearEquiv ℂ (WithFunctional f A) :
    (WithFunctional f A) →ₗ⋆[ℂ] (WithFunctional f A)) |>.compr₂ₛₗ f

@[simp]
theorem mySesquilinear_apply (f : A →ₚ[ℂ] ℂ) (x y : A) :
  mySesquilinear f x y = f (star x * y) := rfl
-- End code from Eric Wieser -
-/

/-
example (a b : A) : norm (f (star b * a)) ^2 ≤ f (star b * b) * f (star a * a) := by
  let mip := myInnerProductSpace f (A := A)
  have cs := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) a b
  sorry


#check let mip := myInnerProductSpace f (A := A)
  InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) p q

let mip := myInnerProductSpace f (A := A)
#check inner_mul_inner_self_le (𝕜 := ℂ) p q

#check InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) p q




#check myInnerProductSpace f -- PreInnerProductSpace.Core ℂ A
#check (myInnerProductSpace f).smul_left
#check (myInnerProductSpace f).inner
#check (myInnerProductSpace f)
-/
