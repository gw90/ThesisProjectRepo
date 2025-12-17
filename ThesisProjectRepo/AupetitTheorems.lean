import ThesisProjectRepo.AupetitThrm6_2_15

open ComplexConjugate
open scoped ComplexOrder
open Complex

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

lemma aux (a b : A) (h : f (star a * a) = 0) : f (star a * b) = 0 := by
  have hab := aup_6_2_15ii f (star a) (star b)
  rw [star_star, star_star] at hab
  rw [h, zero_mul] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

def N (f : A →ₚ[ℂ] ℂ) : Submodule ℂ A where
  carrier := {a : A | f (star a * a) = 0}
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at ha
    rw [Set.mem_setOf_eq] at hb
    have hab := aux f a b ha
    have hba := aux f b a hb
    rw [Set.mem_setOf_eq, star_add, left_distrib, right_distrib, right_distrib,
      ← add_assoc, map_add, map_add, map_add, ha, hb, add_zero, zero_add, hba, hab, add_zero]
  zero_mem' := by simp;
  smul_mem' := by
    intro c x hx
    rw [Set.mem_setOf_eq] at hx
    rw [Set.mem_setOf_eq, star_smul, RCLike.star_def, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, map_smul, smul_eq_mul, mul_eq_zero, map_smul,
      smul_eq_mul, mul_eq_zero, map_eq_zero, or_self_left]
    right
    exact hx
