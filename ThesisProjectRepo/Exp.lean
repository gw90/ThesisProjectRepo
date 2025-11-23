import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.UniformSpace.Completion

open UniformSpace

variable {A : Type*} [AddCommMonoid A] [Module ℂ A] [UniformSpace A] [AddCommMonoid (Completion A)] [Module ℂ (Completion A)]
variable {B : Type*} [AddCommMonoid B] [Module ℂ B] [UniformSpace B] [AddCommMonoid (Completion B)] [Module ℂ (Completion B)]
variable (f : A →ₗ[ℂ] B)
noncomputable instance : UniformContinuous f := sorry

noncomputable
def linearMap_coe : (Completion A) →ₗ[ℂ] (Completion B) where
  toFun := Completion.map f
  map_add' x y := by
    #check UniformSpace.Completion.map_unique
    have (x : A): (Completion.map (f)) x = f x := Completion.map_coe (instUniformContinuousCoeLinearMapComplexId_thesisProjectRepo f) x
    refine UniformSpace.Completion.induction_on x ?_ ?_ (α := A)
    · refine isClosed_eq ?_ ?_
      · refine Continuous.comp' ?_ ?_
        · exact Completion.continuous_map
        sorry
      sorry -- should be closed because it is everything and its own closure
    intro a
    refine UniformSpace.Completion.induction_on y ?_ ?_ (α := A)
    · sorry
    intro b
    have p (a b : A) : (a : Completion A) + ↑b = ↑(a + b) := by sorry
    rw [this a, this b, p, this (a + b)]
    simp
    sorry
  map_smul' c y := by
    simp

    sorry
