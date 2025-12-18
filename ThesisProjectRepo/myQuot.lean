import ThesisProjectRepo.AupetitTheorems
import Mathlib.Analysis.InnerProductSpace.Completion
import ThesisProjectRepo.AupetitTheorems

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

def WithFunctional (_A : Type*) [CStarAlgebra _A] [PartialOrder _A] (_f : _A →ₚ[ℂ] ℂ) := _A

namespace GNS

/-- The canonical inclusion of `A` into `WithFunctional A f`. -/
def toFunctional : A → WithFunctional A f := id

/-- The canonical inclusion of `WithFunctional A f` into `A`. -/
def ofFunctional : WithFunctional A f → A := id

instance [AddCommGroup A] : AddCommGroup (WithFunctional A f) := ‹AddCommGroup A›
instance [Semiring A] : Semiring (WithFunctional A f) := ‹Semiring A›
instance [NonUnitalNonAssocSemiring A] :
  NonUnitalNonAssocSemiring (WithFunctional A f) := ‹NonUnitalNonAssocSemiring A›
instance [Semiring ℂ] [AddCommGroup A] [Module ℂ A] :
  Module ℂ (WithFunctional A f) := ‹Module ℂ (WithFunctional A f)›
instance : NonUnitalSeminormedRing (WithFunctional A f) := by unfold WithFunctional; infer_instance
instance : CStarAlgebra (WithFunctional A f) := by unfold WithFunctional; infer_instance

instance ofFunctionalLinear : LinearMap (RingHom.id ℂ) (WithFunctional A f) A where
  toFun := ofFunctional f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `WithFunctional.toFunctional` and `WithFunctional.toFunctional` as an equivalence. -/
--@[simps]
protected def equiv : WithFunctional A f ≃ A where
  toFun := ofFunctional f
  invFun := toFunctional f
  left_inv _ := rfl
  right_inv _ := rfl

instance N (f : A →ₚ[ℂ] ℂ) : Submodule ℂ (WithFunctional A f) where
  carrier := {a : (WithFunctional A f) | f (star a * a) = 0}
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at *
    simp [left_distrib, right_distrib, ha, hb, aux]
  zero_mem' := by simp
  smul_mem' c x hx := by
    rw [Set.mem_setOf_eq] at hx
    simp [hx]

-- Begin code from Eric Wieser
-- noncomputability should be fixed in by Eric Wieser's bug fix
noncomputable def mySesquilinear :
  (WithFunctional A f) →ₗ⋆[ℂ] (WithFunctional A f) →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ (WithFunctional A f)).comp
  (starLinearEquiv ℂ (A := (WithFunctional A f)) :
    (WithFunctional A f) →ₗ⋆[ℂ] (WithFunctional A f))
    |>.compr₂ₛₗ (f.comp (ofFunctionalLinear f))

--@[simp]
theorem mySesquilinear_apply (x y : (WithFunctional A f)) :
  mySesquilinear f x y = f (star x * y) := rfl
-- End code from Eric Wieser

-- I believe this sucessfully erases the norm
def myQuot := (WithFunctional A f) ⧸ (N f)

instance : AddCommGroup (myQuot f) := by unfold myQuot; infer_instance
instance : Module ℂ (myQuot f) := by unfold myQuot; infer_instance

theorem helper (a : WithFunctional A f) : N f ≤ LinearMap.ker ((mySesquilinear f a)) := by
  intro b bh
  have hab := aup_6_2_15ii f (star a) (star b)
  rw [star_star, star_star, bh, mul_zero] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

noncomputable def myHalf (p : WithFunctional A f) : WithFunctional A f ⧸ N f →ₗ[ℂ] ℂ
  := Submodule.liftQ (N f) (mySesquilinear f p) (helper f p)

noncomputable instance myHalfSQ :
  LinearMap (starRingEnd ℂ) (WithFunctional A f) (WithFunctional A f ⧸ N f →ₗ[ℂ] ℂ) where
  toFun := myHalf f
  map_add' a b := by
    unfold myHalf
    simp only [map_add]
    ext x
    simp [mySesquilinear_apply]
  map_smul' a b := by
    unfold myHalf
    ext x
    simp [mySesquilinear_apply]

theorem halfHelper : N f ≤ LinearMap.ker (myHalfSQ f) := by
  intro a ah
  change (myHalf f) a = 0
  unfold myHalf
  ext b
  have hab := aup_6_2_15ii f (star a) (star b)
  rw [star_star, star_star, ah, zero_mul] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

noncomputable def myInner := Submodule.liftQ (N f) (myHalfSQ f) (halfHelper f)

noncomputable def myF := f.comp (ofFunctionalLinear f)

theorem helperF : N f ≤ LinearMap.ker (myF f) := by
  intro a ah
  simp only [LinearMap.mem_ker]
  have ahzero : f (star a * a) = 0 := ah
  change f a = 0
  have hab := aup_6_2_15ii f (1) (star a)
  rw [star_star, ah, mul_zero] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero, one_mul] at hab

noncomputable def liftedF := Submodule.liftQ (N f) (myF f) (helperF f)

theorem fEquiv (a b : WithFunctional A f) :
  ((myInner f) (Submodule.Quotient.mk a)) (Submodule.Quotient.mk b) = mySesquilinear f a b := by rfl

noncomputable instance myInnerProductSpace : InnerProductSpace.Core ℂ (myQuot f) where
  inner a b := myInner f a b
  conj_inner_symm a b := by
    induction a using Submodule.Quotient.induction_on with | _ a
    induction b using Submodule.Quotient.induction_on with | _ b
    simp [fEquiv f a b, fEquiv f b a, mySesquilinear_apply, ← aupetit_6_2_15i f (star b * a)]
  re_inner_nonneg a := by
    induction a using Submodule.Quotient.induction_on with | _ a
    have zeroleq : 0 ≤ f (star a * a) :=
      PositiveLinearMap.map_nonneg f (star_mul_self_nonneg (ofFunctional f a))
    have := fOfxStarxIsReal f (star a)
    rw [star_star] at this
    rw [← this] at zeroleq
    simp [fEquiv f a a, mySesquilinear_apply, Complex.zero_le_real.mp zeroleq]
  add_left a b c := by simp
  smul_left a b c := by simp
  definite a := by
    induction a using Submodule.Quotient.induction_on
    exact (Submodule.Quotient.mk_eq_zero (N f)).mpr

noncomputable instance : NormedAddCommGroup (myQuot f) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := myInnerProductSpace f)
noncomputable instance : InnerProductSpace ℂ (myQuot f) :=
  InnerProductSpace.ofCore (myInnerProductSpace f).toCore
noncomputable instance : NormedSpace ℂ (myQuot f) := by infer_instance

def H := UniformSpace.Completion (myQuot f)

noncomputable instance : UniformSpace (H f) := by unfold H; infer_instance
instance : CompleteSpace (H f) := by unfold H; infer_instance
noncomputable instance : NormedAddCommGroup (H f) := by unfold H; infer_instance
noncomputable instance : InnerProductSpace ℂ (H f) := by unfold H; infer_instance
-- or UniformSpace.Completion.innerProductSpace (E := myQuot f) (𝕜 := ℂ)

protected
instance HilbertSpaceFromFunctional : HilbertSpace ℂ (H f) where

#check GNS.HilbertSpaceFromFunctional f

def aToMyQuot (a : A) : myQuot f := Submodule.Quotient.mk a
def myQuotToH (a : myQuot f) : H f := UniformSpace.Completion.coe' a
def aToH (a : A) : H f := myQuotToH f (aToMyQuot f a)

variable (b : WithFunctional A f)
#check (myInnerProductSpace f).inner (Submodule.Quotient.mk b) (Submodule.Quotient.mk b)

@[simp]
theorem myInner_apply (a : WithFunctional A f) (b : WithFunctional A f) :
  (myInnerProductSpace f).inner (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)
    = f (star a * b) := by rfl

end GNS
