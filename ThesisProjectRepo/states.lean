import Mathlib.Algebra.DirectSum.Basic
import ThesisProjectRepo.Morphism
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

open ComplexConjugate
open scoped ComplexOrder
open Complex

variable {A : Type*} [CStarAlgebra A] [PartialOrder A]

/--
A state is a unital positive linear functional. That is, it is a PositiveLinearMap from A to ℂ
that maps (1 : A) to 1.
-/
structure State (A : Type*) [CStarAlgebra A] [PartialOrder A]
  extends A →ₚ[ℂ] ℂ , OneHom A ℂ

namespace State

instance : FunLike (State A) A ℂ where
  coe f := (State.toPositiveLinearMap f).toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    exact PositiveLinearMap.ext_iff.mpr (congrFun h)

@[ext]
lemma ext {f g : State A} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

variable (s : State A)
-- make 8.0.16 into two theorems about opnorm =1 and about f(1_A)=1, both return a State

def from_positive_unital_functional (f : A →ₚ[ℂ] ℂ) (unital_hyp : f 1 = 1) : State A :=
  State.mk (A := A) f unital_hyp

theorem state_if_positive_and_unital (f : A →ₚ[ℂ] ℂ) (unital_hyp : f 1 = 1) :
    ∃ (s : State A), (s : A → ℂ) = (f : A → ℂ) := by
  use from_positive_unital_functional f unital_hyp
  exact List.map_inj.mp rfl

@[simp]
lemma maps_one (s : State A) : s 1 = 1 := by
  have (a : A) : s a = s.toOneHom a := by exact DFunLike.congr rfl rfl
  rw [this]
  rw [OneHom.map_one s.toOneHom]

example (f : A →ₚ[ℂ] ℂ) (unital_hyp : f 1 = 1) : f 1 = s 1 := by simp_all

def mk_from_linear_continuous_unital_opNorm_one (f : A →L[ℂ] ℂ) (unital_hyp : f 1 = 1)
    (h_opNorm_one : ‖f‖ = 1) : State A where
  toFun := f
  map_add' x y := map_add f x y
  map_smul' x y := ContinuousLinearMap.map_smul_of_tower f x y
  map_one' := Complex.ext (congrArg re unital_hyp) (congrArg im unital_hyp)
  monotone' x y := by sorry--Finish this from Prop 8.0.16

--variable [StarOrderedRing A] --[Nontrivial A] -- why don't we have nontrivial by default if unital?

#check spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius

def ns (n : ℕ) : ℕ := (2 ^ n)

-- moving the exponent outside requires self-adjoint and non-negative
-- is the square of a self-adjoint element always non-negative?
/-variable (a : A) (h : IsSelfAdjoint a) --(ha : 0 ≤ a)
lemma a_nonneg : 0 ≤ a ^ 2 := by sorry
lemma zero_le_2 : 0 < (2 : ℝ) := by exact zero_lt_two-/
--#check CFC.norm_nnrpow a (r := 2) zero_lt_two

open Filter
-- 5.0.14
omit [PartialOrder A]
theorem Aguilar_5_0_14_case_sa {a : A} (h : IsSelfAdjoint a) : nnnorm a = spectralRadius ℂ a := by
  exact Eq.symm (IsSelfAdjoint.spectralRadius_eq_nnnorm h)

/-
have gelfand_formula := spectrum.gelfand_formula a
  have sub_seq := IsSelfAdjoint.norm_pow_two_pow h
  have sub_seq' := IsSelfAdjoint.nnnorm_pow_two_pow h
  #check Filter.tendsto_of_subseq_tendsto
  #check (ns : ℕ → ℕ)

-/
/-- In a C⋆-algebra, the spectral radius of the adjoint of an element times itself is equal to the
square of that element's norm.
-/
theorem spectralRadius_toReal_star_self_mul_self_eq_normSq (a : A) :
    (spectralRadius ℂ (star a * a)).toReal = ‖a‖ ^ 2 := by
  rw [IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm (IsSelfAdjoint.star_mul_self a),
    CStarRing.norm_star_mul_self, ← pow_two]

theorem sqrt_spectralRadius_toReal_star_self_mul_self_eq_norm (a : A) :
    Real.sqrt ((spectralRadius ℂ (star a * a)).toReal) = norm a :=
  (Real.sqrt_eq_iff_eq_sq ENNReal.toReal_nonneg (norm_nonneg a)).mpr
    (spectralRadius_toReal_star_self_mul_self_eq_normSq a)

#check NonUnitalAlgHomClass

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
theorem StarAlgHom_Bounded (f : NonUnitalStarAlgHom ℂ A B) (x : A) :
    (‖f x‖ ≤ 1 * ‖x‖) := by simp [NonUnitalStarAlgHom.norm_apply_le]

theorem StarAlgHom_Continuous (f : NonUnitalStarAlgHom ℂ A B) : Continuous (f : A → B) :=
  continuous_of_linear_of_bound (f.map_add) (f.map_smul) (StarAlgHom_Bounded f)

-- StarAlgHoms are basically already continuous

end State
