import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.UniformSpace.Completion

-- Setup
variable {A : Type*} [AddCommMonoid A] [Module ℂ A] [UniformSpace A]
def H := UniformSpace.Completion (A)
instance : AddCommMonoid (H (A := A)) := sorry
instance : Module ℂ (H (A := A)) := sorry
def Tlin : A →ₗ[ℂ] A := sorry

-- Questions
noncomputable
def T : (H (A := A)) →ₗ[ℂ] (H (A := A)) where
  toFun := UniformSpace.Completion.map (Tlin) (α := A) (β := A)
  map_add' := sorry -- is there a way to conicesly prove this
  map_smul' := sorry -- and this?

noncomputable
def T' : (H (A := A)) →ₗ[ℂ] (H (A := A)) := by exact T -- Is there something I could put here?
