import ThesisProjectRepo.AupetitTheorems
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.UniformSpace.Completion

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
    rw [Set.mem_setOf_eq] at ha
    rw [Set.mem_setOf_eq] at hb
    have hab := aux f a b ha
    have hba := aux f b a hb
    rw [Set.mem_setOf_eq, star_add, left_distrib, right_distrib, right_distrib,
      ← add_assoc, map_add, map_add, map_add, ha, hb, add_zero, zero_add, hba,
      hab, add_zero]
  zero_mem' := by simp
  smul_mem' c := by
    intro x hx
    rw [Set.mem_setOf_eq] at hx
    rw [Set.mem_setOf_eq, star_smul, RCLike.star_def, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, map_smul, smul_eq_mul, mul_eq_zero, map_smul,
      smul_eq_mul, mul_eq_zero, map_eq_zero, or_self_left]
    right
    exact hx

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
  rw [LinearMap.mem_ker, mySesquilinear_apply]
  have bhzero : f (star b * b) = 0 := bh
  have hab := aup_6_2_15ii f (star a) (star b)
  rw [star_star, star_star] at hab
  rw [bh, mul_zero] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

noncomputable def myHalf (p : WithFunctional A f) : WithFunctional A f ⧸ N f →ₗ[ℂ] ℂ
  := Submodule.liftQ (N f) (mySesquilinear f p) (helper f p)

noncomputable instance myHalfSQ :
  LinearMap (starRingEnd ℂ) (WithFunctional A f) (WithFunctional A f ⧸ N f →ₗ[ℂ] ℂ) where
  toFun := myHalf f
  map_add' a b := by
    unfold myHalf
    simp_all only [map_add]
    ext x : 2
    simp_all only [Submodule.liftQ_mkQ, LinearMap.add_apply, mySesquilinear_apply,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
  map_smul' a b := by
    unfold myHalf
    simp_all only [LinearMap.map_smulₛₗ]
    ext x : 2
    simp_all only [Submodule.liftQ_mkQ, LinearMap.smul_apply, mySesquilinear_apply,
      smul_eq_mul, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.liftQ_apply]

theorem halfHelper : N f ≤ LinearMap.ker (myHalfSQ f) := by
  intro a ah
  simp only [LinearMap.mem_ker]
  change (myHalf f) a = 0
  unfold myHalf
  have : f (star a * a) = 0 := ah
  ext b
  rw [Submodule.liftQ_mkQ, mySesquilinear_apply, LinearMap.zero_comp, LinearMap.zero_apply]

  have hab := aup_6_2_15ii f (star a) (star b)
  rw [star_star, star_star] at hab
  rw [ah, zero_mul] at hab
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
    · induction b using Submodule.Quotient.induction_on with | _ b
      · rw [fEquiv f a b, fEquiv f b a]
        simp only [mySesquilinear_apply]
        rw [← aupetit_6_2_15i f (star b * a)]
        simp only [star_mul, star_star]
  re_inner_nonneg a := by
    induction a using Submodule.Quotient.induction_on with | _ a
    · rw [fEquiv f a a, mySesquilinear_apply, RCLike.re_to_complex]
      have nonneg : 0 ≤ star (ofFunctional f a) * (ofFunctional f a) :=
        star_mul_self_nonneg (ofFunctional f a)
      have := fOfxStarxIsReal f (star a)
      simp at this
      have zeroleq : 0 ≤ f (star a * a) := PositiveLinearMap.map_nonneg f nonneg
      rw [← this] at zeroleq
      exact Complex.zero_le_real.mp zeroleq
  add_left a b c := by
    induction a using Submodule.Quotient.induction_on with | _ a
    · induction b using Submodule.Quotient.induction_on with | _ b
      · induction c using Submodule.Quotient.induction_on with | _ c
        · rw [map_add, LinearMap.add_apply]
  smul_left a b c := by
    induction a using Submodule.Quotient.induction_on with | _ a
    · induction b using Submodule.Quotient.induction_on with | _ b
      · rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  definite a := by
    induction a using Submodule.Quotient.induction_on with | _ a
    · rw [fEquiv f a a, mySesquilinear_apply]
      intro ha
      have : a ∈ N f := ha
      apply (Submodule.Quotient.mk_eq_zero (N f) (x := a)).mpr
      assumption

noncomputable instance : NormedAddCommGroup (myQuot f) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := myInnerProductSpace f)
noncomputable instance : InnerProductSpace ℂ (myQuot f) :=
  InnerProductSpace.ofCore (myInnerProductSpace f)

def H := UniformSpace.Completion (myQuot f)

noncomputable instance : UniformSpace (H f) := by unfold H; infer_instance
instance : CompleteSpace (H f) := by unfold H; infer_instance
noncomputable instance : NormedAddCommGroup (H f) := by unfold H; infer_instance
noncomputable instance : InnerProductSpace ℂ (H f) := by unfold H; infer_instance

protected
instance HilbertSpaceFromFunctional : HilbertSpace ℂ (H f) where
#check GNS.HilbertSpaceFromFunctional f

def aToMyQuot (a : A) : myQuot f := Submodule.Quotient.mk a
def myQuotToH (a : myQuot f) : H f := UniformSpace.Completion.coe' a
def aToH (a : A) : H f := myQuotToH f (aToMyQuot f a)

end GNS

-- To-do: Move on to Aupetit 6.2.19
