import ThesisProjectRepo.AupetitTheorems
import Mathlib.Analysis.InnerProductSpace.Completion

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
@[simps]
protected def equiv : WithFunctional A f ≃ A where
  toFun := ofFunctional f
  invFun := toFunctional f
  left_inv _ := rfl
  right_inv _ := rfl

def myIdeal := N f

instance mySubModule (f : A →ₚ[ℂ] ℂ) : Submodule ℂ (WithFunctional A f) where
  carrier := {a : (WithFunctional A f) | f (star a * a) = 0}
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at ha
    rw [Set.mem_setOf_eq] at hb
    rw [Set.mem_setOf_eq, star_add, left_distrib, right_distrib, right_distrib,
      ← add_assoc, map_add, map_add, map_add, ha, hb, add_zero, zero_add]

    have hab := aupetit_6_2_15ii f (star a) (star b)
    rw [star_star, star_star] at hab
    rw [ha, hb, zero_mul] at hab
    norm_cast at hab
    rw [sq_nonpos_iff, norm_eq_zero] at hab

    have hba := aupetit_6_2_15ii f (star b) (star a)
    rw [star_star, star_star] at hba
    rw [ha, hb, zero_mul] at hba
    norm_cast at hba
    rw [sq_nonpos_iff, norm_eq_zero] at hba

    rw [hba, hab]
    norm_num -- could be simp too
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    rw [Set.mem_setOf_eq] at hx
    rw [Set.mem_setOf_eq, star_smul, RCLike.star_def, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, map_smul, smul_eq_mul, mul_eq_zero, map_smul,
      smul_eq_mul, mul_eq_zero, map_eq_zero, or_self_left]
    right
    exact hx

-- Begin code from Eric Wieser
-- noncomputability should be fixed in by Eric Wieser's bug fix
noncomputable def mySesquilinear (f : A →ₚ[ℂ] ℂ) :
  (WithFunctional A f) →ₗ⋆[ℂ] (WithFunctional A f) →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ (WithFunctional A f)).comp
  (starLinearEquiv ℂ (A := (WithFunctional A f)) :
    (WithFunctional A f) →ₗ⋆[ℂ] (WithFunctional A f))
    |>.compr₂ₛₗ
    (f.comp (ofFunctionalLinear f))

@[simp]
theorem mySesquilinear_apply (f : A →ₚ[ℂ] ℂ) (x y : (WithFunctional A f)) :
  mySesquilinear f x y = f (star x * y) := rfl
-- End code from Eric Wieser

-- I believe this sucessfully erases the norm
def myQuot := (WithFunctional A f) ⧸ (mySubModule f)
#check myQuot f


def toQuot : (myQuot f) → (WithFunctional A f) ⧸ (mySubModule f) := id
def toMyQuot : (WithFunctional A f) ⧸ (mySubModule f) → (myQuot f) := id
def modOut := Submodule.Quotient.mk (M := (WithFunctional A f)) (p := (mySubModule f))

instance : AddCommGroup (myQuot f) := by unfold myQuot; infer_instance
instance : Module ℂ (myQuot f) := by unfold myQuot; infer_instance

theorem helper (a : WithFunctional A f) : mySubModule f ≤ LinearMap.ker ((mySesquilinear f a)) := by
  intro b bh
  rw [LinearMap.mem_ker, mySesquilinear_apply]
  have bhzero : f (star b * b) = 0 := by exact bh
  have hab := aupetit_6_2_15ii f (star a) (star b)
  rw [star_star, star_star] at hab
  rw [bh, mul_zero] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

theorem helper' : mySubModule f ≤ LinearMap.ker (mySesquilinear f) := by
  intro a ah
  ext b
  rw [mySesquilinear_apply]
  simp only [LinearMap.zero_apply]
  have bhzero : f (star a * a) = 0 := by exact ah

  have hab := aupetit_6_2_15ii f (star a) (star b)
  rw [star_star, star_star] at hab
  rw [ah, zero_mul] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

theorem helper2 (a : myQuot f) :
  mySubModule f ≤ LinearMap.ker (((mySubModule f).liftQ (mySesquilinear f) (helper' f)) a) := by
  intro b bh
  rw [LinearMap.mem_ker]
  have bhzero : f (star b * b) = 0 := by exact bh


  sorry

noncomputable def myHalf (p : WithFunctional A f) : WithFunctional A f ⧸ mySubModule f →ₗ[ℂ] ℂ
  := Submodule.liftQ (mySubModule f) (mySesquilinear f p) (helper f p)
#check myHalf f -- WithFunctional A f → WithFunctional A f ⧸ mySubModule f →ₗ[ℂ] ℂ
noncomputable instance myHalfSQ :
  LinearMap (starRingEnd ℂ) (WithFunctional A f) (WithFunctional A f ⧸ mySubModule f →ₗ[ℂ] ℂ) where
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

#check myHalfSQ f -- now lift it
#check Submodule.liftQ (mySubModule f) (myHalfSQ f)

theorem halfHelper : mySubModule f ≤ LinearMap.ker (myHalfSQ f) := by
  intro a ah
  simp only [LinearMap.mem_ker]
  change (myHalf f) a = 0
  unfold myHalf
  have : f (star a * a) = 0 := ah
  ext b
  rw [Submodule.liftQ_mkQ, mySesquilinear_apply, LinearMap.zero_comp, LinearMap.zero_apply]


  have hab := aupetit_6_2_15ii f (star a) (star b)
  rw [star_star, star_star] at hab
  rw [ah, zero_mul] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

noncomputable def myInner := Submodule.liftQ (mySubModule f) (myHalfSQ f) (halfHelper f)

noncomputable def myF := f.comp (ofFunctionalLinear f)
-- make a lifted f
theorem helperF : mySubModule f ≤ LinearMap.ker (myF f) := by
  intro a ah
  simp only [LinearMap.mem_ker]
  have ahzero : f (star a * a) = 0 := by exact ah
  change f a = 0

  have hab := aupetit_6_2_15ii f (1) (star a)
  rw [star_star] at hab
  rw [ah, mul_zero] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero, one_mul] at hab

noncomputable def liftedF := Submodule.liftQ (mySubModule f) (myF f) (helperF f)

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
      have : a ∈ mySubModule f := by exact ha
      apply (Submodule.Quotient.mk_eq_zero (mySubModule f) (x := a)).mpr
      assumption

noncomputable def toComplete := InnerProductSpace.ofCore (myInnerProductSpace f)

instance : SeminormedAddCommGroup (myQuot f) where
  norm a := (myInner f a a).re
  dist_self a := by simp
  dist_comm a b := by
    induction a using Submodule.Quotient.induction_on with | _ a
    · induction b using Submodule.Quotient.induction_on with | _ b
      · rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_sub]
        simp only [fEquiv f, mySesquilinear_apply]
        have : 1 * (a-b) = a-b := by simp
        nth_rw 1 [← this]
        have : (1 : A) = -1 * -1 := by simp
        rw [this]
        have aux : -1 * (a - b) = b - a := by simp
        rw [mul_assoc, aux]
        have : star (-1 * (b - a)) = -1 * star (b - a) := by simp
        rw [this]
        have : -1 * star (b - a) = star (b - a) * -1 := by simp
        rw [this, mul_assoc, aux]
  dist_triangle a b c := by
    induction a using Submodule.Quotient.induction_on with | _ a
    · induction b using Submodule.Quotient.induction_on with | _ b
      · induction c using Submodule.Quotient.induction_on with | _ c
        · repeat rw [← Submodule.Quotient.mk_sub]
          simp only [fEquiv, mySesquilinear_apply]
          sorry

#check toComplete f
#check UniformSpace.Completion.innerProductSpace

end WithFunctional
