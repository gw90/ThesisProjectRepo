import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Operations
import Mathlib.Algebra.Star.Subalgebra

section
variable (α : Type*) [A : CStarAlgebra α] -- unital complex C*-algebra
variable [PartialOrder α] [PartialOrder ℂ]
variable (a b c : α)
variable [IsStarNormal c]

#check A.mul_one
#check a * b
#check spectrum ℂ a
#check PositiveLinearMap
#check A.one
#check A.zero
#check star a
#check spectrum ℂ a
#check CStarAlgebra.approximateUnit

#check StrongDual ℂ α

example : 2 ∉ {x : ℝ | x = 1} := by simp

example : c * star c = star c * c := by exact Eq.symm (star_comm_self' c)

example : a = 0 * star b + a := by simp
variable (f : StrongDual ℂ α) -- continuous linear functional
variable (g : α →L[ℂ] ℂ) -- continuous linear functional
variable (h : α →ₚ[ℂ] ℂ) -- positive continuous linear functional?
-- (but we had to put partial orders on stuf. why weren't they already there?)
-- will I need to specify the partial order?
#check f
#check f a
#check g
#check g a
#check h
#check h a

def sloop := fun (x : α) ↦ f (star x * x)
#print sloop
#check sloop α f b
def Nf := Set.preimage (sloop α f) {0}
#check Nf

noncomputable
example : α →* ℂ := by exact Algebra.norm ℂ

-- I think the kernel of a homomorphism should be a subring/StarSubalgebra
-- by Subring.comap in Mathlib.Algebra.Ring.Subring.Basic

theorem part1 : Ideal Nf := by -- WTS is norm-closed left ideal, but first we have to show its a ring
  sorry

def sleep := sloop α f
#check sleep

def meep {A : CStarAlgebra α} := fun x : α ↦ f x
#print meep
#check (meep α f) a
#check f (star a * a)
def morp {α : Type*} := fun x : α ↦ x
#print morp
#check morp b


example (x : α) : ‖star x * x‖ = ‖x‖^2 ↔ ‖star x * x‖ = ‖star x‖ * ‖x‖ := by
  rw [norm_star x, pow_two ‖x‖]

example : IsCompact (spectrum ℂ a) := by sorry


variable {A₁ A₂ B₁ B₂ : Type*}

variable [CStarAlgebra A₁] [CStarAlgebra A₂] [PartialOrder A₁]
  [StarOrderedRing A₁] [PartialOrder A₂] [StarOrderedRing A₂]
#check A₁ →ₚ[ℂ] A₂

example : a * a = a^2 := by exact Eq.symm (pow_two a)

def whateverthisis {G : Type*} [CStarAlgebra G] (H : Subring G) : Subring G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = h}
  mul_mem' := by aesop
  one_mem' := by simp
  add_mem' := by simp; aesop
  zero_mem' := by simp
  neg_mem' := by simp


example {G : Type*} [CStarAlgebra G] (H : Subring G) : Ring H := inferInstance

end
