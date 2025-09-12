import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Topology.Defs.Filter
import Mathlib.Data.Set.Operations
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.Star -- conjugate linear maps

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [PartialOrder ℂ]
variable [NormedAlgebra ℂ A] -- what does this do? Is it necessary?
variable [StarOrderedRing A] -- Figure out what this does/means
variable (f : A →ₚ[ℂ] ℂ)
variable (p : A) (q : A) -- for experimentation. remove later
set_option linter.unusedSectionVars false -- remove this at the end
-- maybe not the right Cauchy-Schwartz at Mathlib.Analysis.InnerProductSpace.Basic
theorem posEl (a : A) : 0 ≤ (star a) * a := by
  exact star_mul_self_nonneg a

theorem posMeaning (a : A) (h : 0 ≤ a) (f : A →ₚ[ℂ] ℂ) : 0 ≤ f a := by
  exact PositiveLinearMap.map_nonneg f h

theorem posposEl (a : A) : 0 ≤ f (star a * a) := by
  have : 0 ≤ star a * a := star_mul_self_nonneg a
  exact PositiveLinearMap.map_nonneg f this
-- just change RingHom.id to starRingEnd ?
-- The sesquilinear map I want:
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/CStarAlgebra/Module/Defs.html#CStarModule.inner%E2%82%9B%E2%82%97
def own' := fun [b : A] [f : A →ₚ[ℂ] ℂ] (a : A) => f (star b * a)
#check own'
#check LinearMap (RingHom.id ℂ) A ℂ
def helperMap {b : A} {f : A →ₚ[ℂ] ℂ} : LinearMap (RingHom.id ℂ) A ℂ where
  toFun := fun (a : A) => f (star b * a)
  map_add' := by
    intro x y
    rw [left_distrib]
    exact map_add f (star b * x) (star b * y)
  map_smul' := by simp

#check helperMap

-- the inner map should be linear, the outer map should be conjguate linear
-- this means first paramter is conjguate linear, second is linear

variable (h : A →ₚ[ℂ] ℂ)
def myInner := fun (f : A →ₚ[ℂ] ℂ) (b : A) (a : A) => f (star b * a)
#check (myInner f : A → A → ℂ) -- A → A → ℂ
#check (myInner f : A → A → ℂ) p -- A → ℂ
-- parameter a should be linear
def myInnerHelper (f : A →ₚ[ℂ] ℂ) (a : A) : LinearMap (RingHom.id ℂ) A ℂ where
  toFun := (myInner f : A → A → ℂ) a -- A → ℂ
  map_add' := by
    intro x y
    dsimp [myInner]
    rw [mul_add]
    exact map_add f (star a * x) (star a * y)
  map_smul' := by
    intro m x
    dsimp [myInner, RingHom.id]
    simp
#check (myInnerHelper f) p -- A →ₗ[ℂ] ℂ
-- paramter b should be conjugate linear
def mySesquiLinear (f : A →ₚ[ℂ] ℂ) {b : A} : LinearMap (starRingEnd ℂ) A (A →ₗ[ℂ] ℂ) where
  toFun := (myInnerHelper f)
  map_add' := by
    intro x y
    ext a
    dsimp [myInnerHelper, myInner]
    rw [star_add, add_mul]
    exact map_add f (star x * a) (star y * a)
  map_smul' := by
    intro m x
    ext a
    simp [myInnerHelper, myInner]

#check mySesquiLinear f


-- define whole function (f a b) and then show that (f a) is linear to show (f)
-- is bilinear/conjugate linear

#check LinearMap.BilinForm ℂ A
#check fun (a : A) => fun (b : A) => f (star b * a)
#check fun (a : A) => fun (b : A) => f (star b * a)
open PositiveLinearMapClass
#check toPositiveLinearMap f
#check LinearMap (RingHom.id ℂ) A ℂ
#check A →ₗ[ℂ] A
#check ((f : A →ₚ[ℂ] ℂ) : A →ₗ[ℂ] ℂ)

#check fun (a : A) => (fun (b : A) => f b)
#check fun (a : A) => ((f : A →ₚ[ℂ] ℂ) : A →ₗ[ℂ] ℂ)
#check fun (a : A) (b : A) => f (star b * a)
#check fun (b : A) => helperMap


-- first show that f(star ⬝ * a) is linear
-- maybe constructing for linearity in the wrong paramter
-- (was incorrectly considering the conjugate linear b)
-- Mathlib.Algebra.Star.Basic - read up on conjugate linear maps
/-
def glorp : LinearMap.BilinForm ℂ A where
  toFun := sorry
  map_add' := sorry
  map_smul' := sorry

-- this is probably the theorem I need to math 138 8.0.10
#check LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le

noncomputable
def semiInnerf := LinearMap.mk₂ ℂ (fun (a : A) (b : A) => f (star b * a))
  sorry sorry sorry sorry sorry sorry
-/
lemma add_mem_helper (a b : A) : a ∈ {a | f (star a * a) = 0}
  → b ∈ {a | f (star a * a) = 0} → a + b ∈ {a | f (star a * a) = 0} := by
  simp
  intro h1 h2
  rw [mul_add, add_mul, add_mul, ← add_assoc]
  have : f (star a * a + star b * a + star a * b + star b * b)
    = f (star a * a) + f (star b * a) + f (star a * b) + f (star b * b) := by simp
  rw [this]
  rw [h1, h2]
  ring_nf
  sorry

lemma smul_mem_helper (b : A) {a : A} : a ∈ {a | f (star a * a) = 0}
  → b • a ∈ {a | f (star a * a) = 0} := by
  simp
  intro h
  sorry

-- From Aupetit leamm 6.2.18
def N : Ideal A where
  carrier := {a : A | f (star a * a) = 0}
  add_mem' := by intro a b; exact add_mem_helper f a b
  zero_mem' := by simp;
  smul_mem' := by intro b; exact smul_mem_helper f b

--theorem aupetit6_2_18_closed : IsClosed {a : A | f (star a * a) = 0} := by sorry

#check N f
#check Ideal.coe_closure (N f)
#check (N f).closure
#check ((N f) : Set A)

theorem aupetit6_2_18_closed' : (N f) = (N f).closure := by sorry

theorem aupetit6_2_18_closed : IsClosed ((N f) : Set A) := by sorry

/-
To-do: define A/N f, and the inner product on it
- define the semi-inner product/positive semidefinite sesquilinar form, from 138 8.0.10
- or maybe define the full inner product from 8.0.14
- set up all relevant statements with sorries first
- maybe refactor so that the ideal definition is actually easy to prove
- make the partial order on the CStarAlgebra explicit so that I can use
  non-negativity of certain elements, like a* a (I think StarOrderedRing does this)
- enable the better star notation
-/
