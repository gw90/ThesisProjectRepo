import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

open ComplexConjugate
open scoped ComplexOrder
open Complex

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

lemma f_of_x_star_x_is_real (x : A) : (f (x * star x)).re = f (x * star x) := by
  have fstareqfnostar : f (star (x * star x)) = f (x * star x)
    := congrArg (⇑f) (star_mul_star x x)
  rw [(map_star f (x * star x))] at fstareqfnostar
  apply Complex.conj_eq_iff_re.mp fstareqfnostar

/--
If `f` is a positive map, then `f (star a * b)` is a semi-inner product
(positive semidefinite sesquilinear form) which makes `A` into a `PreInnerProductSpace`.
-/
noncomputable instance PreInnerProductSpaceOnA : PreInnerProductSpace.Core ℂ (A) where
  inner a b := f (star a * b)
  conj_inner_symm x y := by apply star_inj.mp; rw [← map_star f (star x * y)]; simp
  re_inner_nonneg x :=
    (RCLike.re_nonneg_of_nonneg (x := f (star x * x))
      (LE.le.isSelfAdjoint (PositiveLinearMap.map_nonneg f (star_mul_self_nonneg x)))).mpr
        (PositiveLinearMap.map_nonneg f (star_mul_self_nonneg x))
  add_left x y z := by rw [star_add, add_mul, map_add]
  smul_left x y r := by simp

/--
The semi-inner product `f (star a * b)` satisfies a version of the Cauchy-Schwarz inequality.
-/
theorem f_inner_mul_inner_self_le (a b : A) :
    ‖f (star a * b)‖ * ‖f (star b * a)‖ ≤ RCLike.re (f (star a * a)) * RCLike.re (f (star b * b)) :=
  RCLike.ofReal_le_ofReal.mp
    (InnerProductSpace.Core.inner_mul_inner_self_le (c := PreInnerProductSpaceOnA f) a b)

/--
The semi-inner product `f (star a * b)` satisfies the Cauchy-Schwarz inequality.
-/
theorem f_inner_norm_sq_self_le (a b : A) :
    norm (f (star a * b)) ^ 2 ≤ f (star a * a) * f (star b * b) := by
  have cs := f_inner_mul_inner_self_le f a b
  apply Complex.real_le_real.mpr at cs
  have inner_re := InnerProductSpace.Core.inner_self_ofReal_re (c := PreInnerProductSpaceOnA f)
  nth_rw 2 [Complex.ofReal_mul] at cs
  have conj_symm := PreInnerProductSpace.Core.conj_inner_symm (PreInnerProductSpaceOnA f) a b
  have norm_eq_conj_norm : ↑‖(starRingEnd ℂ) ((PreInnerProductSpaceOnA f).inner b a)‖ =
    ↑‖(PreInnerProductSpaceOnA f).inner b a‖ := by simp
  have (a : A) (b : A) : (PreInnerProductSpaceOnA f).inner a b = f (star a * b) := by exact rfl
  simp_all only [ofReal_mul, RCLike.re_to_complex, coe_algebraMap, ← pow_two]

lemma f_star_a_a_zero_imp_f_star_a_b_zero
  (a b : A) (h : f (star a * a) = 0) : f (star a * b) = 0 := by
  have hab := f_inner_norm_sq_self_le f a b
  rw [h, zero_mul] at hab
  rw [← norm_eq_zero]
  norm_cast at hab
  exact (_root_.sq_nonpos_iff ‖f (star a * b)‖).mp hab

-- Maybe in CStarAlgebra.Hom, add Theorem 5.0.16
