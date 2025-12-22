import Mathlib.Analysis.InnerProductSpace.Completion
import ThesisProjectRepo.HelperTheorems

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
    simp [left_distrib, right_distrib, ha, hb, f_star_a_a_zero_imp_f_star_a_b_zero]
  zero_mem' := by simp
  smul_mem' c x hx := by
    rw [Set.mem_setOf_eq] at hx
    simp [hx]

-- Begin code from Eric Wieser
-- noncomputability should be fixed in by Eric Wieser's bug fix
noncomputable def sq :
  (WithFunctional A f) →ₗ⋆[ℂ] (WithFunctional A f) →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ (WithFunctional A f)).comp
  (starLinearEquiv ℂ (A := (WithFunctional A f)) :
    (WithFunctional A f) →ₗ⋆[ℂ] (WithFunctional A f))
    |>.compr₂ₛₗ (f.comp (ofFunctionalLinear f))


omit [StarOrderedRing A] in
@[simp]
theorem sq_apply (x y : (WithFunctional A f)) :
  sq f x y = f (star x * y) := rfl
-- End code from Eric Wieser

-- I believe this sucessfully erases the norm
def A_mod_N := (WithFunctional A f) ⧸ (N f)

instance : AddCommGroup (A_mod_N f) := by unfold A_mod_N; infer_instance
instance : Module ℂ (A_mod_N f) := by unfold A_mod_N; infer_instance

theorem sq_well_defined (a : WithFunctional A f) : N f ≤ LinearMap.ker ((sq f a)) := by
  intro b bh
  have hab := f_inner_norm_sq_self_le f a b
  rw [bh, mul_zero] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

noncomputable instance half_sq :
  A →ₗ⋆[ℂ] WithFunctional A f ⧸ N f →ₗ[ℂ] ℂ where
  toFun p := Submodule.liftQ (N f) (sq f p) (sq_well_defined f p)
  map_add' a b := by
    simp only [map_add]
    ext x
    simp
  map_smul' a b := by
    ext x
    simp

theorem half_sq_well_defined : N f ≤ LinearMap.ker (half_sq f) := by
  intro a ah
  change Submodule.liftQ (N f) (sq f a) (sq_well_defined f a) = 0
  ext b
  have hab := f_inner_norm_sq_self_le f a b
  rw [ah, zero_mul] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

noncomputable def inner_f := Submodule.liftQ (N f) (half_sq f) (half_sq_well_defined f)

@[simp]
theorem inner_f_def (a b : WithFunctional A f) :
  ((inner_f f) (Submodule.Quotient.mk a)) (Submodule.Quotient.mk b) = sq f a b := by rfl

noncomputable instance A_mod_N_innerProd_space : InnerProductSpace.Core ℂ (A_mod_N f) where
  inner a b := inner_f f a b
  conj_inner_symm a b := by
    induction a using Submodule.Quotient.induction_on with | _ a
    induction b using Submodule.Quotient.induction_on with | _ b
    simp only [sq_apply, inner_f_def f a b]
    change star (f (star b * a)) = f (star a * b)
    rw [← map_star]
    simp
  re_inner_nonneg a := by
    induction a using Submodule.Quotient.induction_on with | _ a
    have zeroleq : 0 ≤ f (star a * a) :=
      PositiveLinearMap.map_nonneg f (star_mul_self_nonneg (ofFunctional f a))
    have := f_of_x_star_x_is_real f (star a)
    rw [star_star] at this
    rw [← this] at zeroleq
    simp [Complex.zero_le_real.mp zeroleq]
  add_left a b c := by simp
  smul_left a b c := by simp
  definite a := by
    induction a using Submodule.Quotient.induction_on
    exact (Submodule.Quotient.mk_eq_zero (N f)).mpr

noncomputable instance : NormedAddCommGroup (A_mod_N f) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := A_mod_N_innerProd_space f)
noncomputable instance : InnerProductSpace ℂ (A_mod_N f) :=
  InnerProductSpace.ofCore (A_mod_N_innerProd_space f).toCore
noncomputable instance : NormedSpace ℂ (A_mod_N f) := by infer_instance

def H := UniformSpace.Completion (A_mod_N f)

noncomputable instance : UniformSpace (H f) := by unfold H; infer_instance
instance : CompleteSpace (H f) := by unfold H; infer_instance
noncomputable instance : NormedAddCommGroup (H f) := by unfold H; infer_instance
noncomputable instance : InnerProductSpace ℂ (H f) := by unfold H; infer_instance
-- or UniformSpace.Completion.innerProductSpace (E := myQuot f) (𝕜 := ℂ)

protected
instance : HilbertSpace ℂ (H f) where


def aToMyQuot (a : A) : A_mod_N f := Submodule.Quotient.mk a
def myQuotToH (a : A_mod_N f) : H f := UniformSpace.Completion.coe' a
def aToH (a : A) : H f := myQuotToH f (aToMyQuot f a)

@[simp]
theorem inner_f_apply_on_quot_mk (a : WithFunctional A f) (b : WithFunctional A f) :
  (A_mod_N_innerProd_space f).inner (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)
    = f (star a * b) := by rfl

end GNS
