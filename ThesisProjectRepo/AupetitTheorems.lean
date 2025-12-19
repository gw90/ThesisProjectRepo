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

noncomputable instance fSemiInnerProdSpace : PreInnerProductSpace.Core ℂ (A) where
  inner a b := f (star a * b)
  conj_inner_symm x y := by apply star_inj.mp; rw [← map_star f (star x * y)]; simp
  re_inner_nonneg x :=
    (RCLike.re_nonneg_of_nonneg (x := f (star x * x))
      (LE.le.isSelfAdjoint (PositiveLinearMap.map_nonneg f (star_mul_self_nonneg x)))).mpr
        (PositiveLinearMap.map_nonneg f (star_mul_self_nonneg x))
  add_left x y z := by rw [star_add, add_mul, map_add]
  smul_left x y r := by simp

theorem CS_with_functional (x y : A) :
  norm (f (star x * y)) ^ 2 ≤ f (star x * x) * f (star y * y) := by
  have cs := InnerProductSpace.Core.inner_mul_inner_self_le (c := fSemiInnerProdSpace f) x y
  apply Complex.real_le_real.mpr at cs
  have inner_re := InnerProductSpace.Core.inner_self_ofReal_re (c := fSemiInnerProdSpace f)
  nth_rw 2 [Complex.ofReal_mul] at cs
  have conj_symm := PreInnerProductSpace.Core.conj_inner_symm (fSemiInnerProdSpace f) x y
  have norm_eq_conj_norm : ↑‖(starRingEnd ℂ) ((fSemiInnerProdSpace f).inner y x)‖ =
    ↑‖(fSemiInnerProdSpace f).inner y x‖ := by simp
  have (a : A) (b : A) : (fSemiInnerProdSpace f).inner a b = f (star a * b) := by exact rfl
  simp_all only [ofReal_mul, RCLike.re_to_complex, coe_algebraMap, ← pow_two]

lemma aux (a b : A) (h : f (star a * a) = 0) : f (star a * b) = 0 := by
  have hab := CS_with_functional f a b
  rw [h, zero_mul] at hab
  rw [← norm_eq_zero, ← sq_nonpos_iff]
  norm_cast at hab

def N (f : A →ₚ[ℂ] ℂ) : Submodule ℂ A where
  carrier := {a : A | f (star a * a) = 0}
  add_mem' := by
    intro a b ha hb
    simp_all [Set.mem_setOf_eq, (aux f a b ha), (aux f b a hb), left_distrib, right_distrib]
  zero_mem' := by simp
  smul_mem' c x hx := by rw [Set.mem_setOf_eq] at hx; simp [hx]
