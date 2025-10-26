import ThesisProjectRepo.AupetitTheorems
set_option linter.unusedSectionVars false -- remove later
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

def WithFunctional (_A : Type*) [CStarAlgebra _A] [PartialOrder _A] (_f : _A →ₚ[ℂ] ℂ) := _A

namespace WithFunctional

/-- The canonical inclusion of `A` into `WithFunctional A f`. -/
def toFunctional : A → WithFunctional A f := id

/-- The canonical inclusion of `WithFunctional A f` into `A`. -/
def ofFunctional : WithFunctional A f → A := id

instance instAddCommGroup [AddCommGroup A] : AddCommGroup (WithFunctional A f) := ‹AddCommGroup A›
instance instSemiring [Semiring A] : Semiring (WithFunctional A f) := ‹Semiring A›
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring A] :
  NonUnitalNonAssocSemiring (WithFunctional A f) := ‹NonUnitalNonAssocSemiring A›
instance instModule [Semiring ℂ] [AddCommGroup A] [Module ℂ A] :
  Module ℂ (WithFunctional A f) := ‹Module ℂ (WithFunctional A f)›

instance ofFunctionalLinear : LinearMap (RingHom.id ℂ) (WithFunctional A f) A where
  toFun := ofFunctional f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `WithFunctional.toFunctional` and `WithFunctional.toFunctional` as an equivalence. -/
@[simps]
protected def equiv : WithFunctional A f ≃ A where
  toFun := ofFunctional f
  invFun := toFunctional f
  left_inv _ := rfl
  right_inv _ := rfl

def myIdeal := N f

instance mySubModule (f : A →ₚ[ℂ] ℂ) : Submodule ℂ (WithFunctional A f) := sorry

-- Begin code from Eric Wieser
-- noncomputability should be fixed in by Eric Wieser's bug fix
noncomputable def mySesquilinear (f : A →ₚ[ℂ] ℂ) :
  (WithFunctional A f) →ₗ⋆[ℂ] (WithFunctional A f) →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ (WithFunctional A f)).comp (starLinearEquiv ℂ (A := (WithFunctional A f)) :
    (WithFunctional A f) →ₗ⋆[ℂ] (WithFunctional A f)) |>.compr₂ₛₗ
    (f.comp (ofFunctionalLinear f))

@[simp]
theorem mySesquilinear_apply (f : A →ₚ[ℂ] ℂ) (x y : (WithFunctional A f)) :
  mySesquilinear f x y = f (star x * y) := rfl
-- End code from Eric Wieser

-- I believe this sucessfully erases the norm
def myQuot := (WithFunctional A f) ⧸ (mySubModule f)

def toQuot : (myQuot f) → (WithFunctional A f) ⧸ (mySubModule f) := id
def toMyQuot : (WithFunctional A f) ⧸ (mySubModule f) → (myQuot f) := id
def modOut := Submodule.Quotient.mk (M := (WithFunctional A f)) (p := (mySubModule f))

instance : AddCommGroup (myQuot f) := by unfold myQuot; infer_instance
instance : Module ℂ (myQuot f) := by unfold myQuot; infer_instance


noncomputable instance myInnerProductSpace : InnerProductSpace.Core ℂ (myQuot f) where
  inner a b := sorry
  conj_inner_symm := sorry
  re_inner_nonneg := sorry
  add_left := sorry
  smul_left := sorry
  definite := sorry

end WithFunctional
