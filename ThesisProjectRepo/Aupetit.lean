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
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Order

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [PartialOrder ℂ] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)
variable (p : A) (q : A) -- for experimentation. remove later
set_option linter.unusedSectionVars false -- remove this at the end

open ComplexConjugate
open ComplexOrder

lemma aupetit_6_2_15lemma (x y : A) (l : ℂ) :
  0 ≤ f (x * star x) + l * f (y * star x) + (conj l) * f (x * star y)
    + l * (conj l) * f (y * star y) := by
  have hnonneg :=  PositiveLinearMap.map_nonneg f (mul_star_self_nonneg (x + (l • y)))
  rw [add_mul, star_add, mul_add, mul_add] at hnonneg
  simp at hnonneg
  have h : f (x * star x) + (starRingEnd ℂ) l * f (x * star y)
      + (l * f (y * star x) + (starRingEnd ℂ) l * (l * f (y * star y)))
    = f (x * star x) + l * f (y * star x) + (starRingEnd ℂ) l * f (x * star y)
      + l * (starRingEnd ℂ) l * f (y * star y) := by ring
  rw [← h]
  assumption

theorem aupetit_6_2_15i (x : A) : f (star x) = conj (f x) := by
  #check aupetit_6_2_15lemma f x 1 1
  -- show that f is StarRingEquiv
  sorry

lemma fOfxStarxIsReal (x : A) : (f (x * star x)).re = f (x * star x) := by
  have xstarmul : star (x * star x) = x * star x := by exact star_mul_star x x
  have fstareqfnostar : f (star (x * star x)) = f (x * star x)
    := by exact congrArg (⇑f) xstarmul
  have fstareqconj: f (star (x * star x)) = conj (f (x * star x))
    := by exact aupetit_6_2_15i f (x * star x)
  rw [fstareqconj] at fstareqfnostar
  have fxisreal := Complex.conj_eq_iff_re.mp fstareqfnostar
  exact fxisreal

lemma fOfxStarxHas0Im (x : A) : (f (x * star x)).im = 0 := by
  have xstarmul : star (x * star x) = x * star x := by exact star_mul_star x x
  have fstareqfnostar : f (star (x * star x)) = f (x * star x)
    := by exact congrArg (⇑f) xstarmul
  have fstareqconj: f (star (x * star x)) = conj (f (x * star x))
    := by exact aupetit_6_2_15i f (x * star x)
  rw [fstareqconj] at fstareqfnostar
  have fxisreal := Complex.conj_eq_iff_im.mp fstareqfnostar
  exact fxisreal

theorem aupetit_6_2_15ii (x y : A) : norm (f (x * star y)) ≤ f (x * star x) * f (y * star y) := by
  have := aupetit_6_2_15lemma f x y (f (x * star y)/((1+2^(1/2))*f (y * star y)))
  have fxisreal := fOfxStarxIsReal f x
  have fyisreal := fOfxStarxIsReal f y

  by_cases fzero : f (x * star y) = 0
  . have fxnonneg := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg x)
    have fynonneg := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg y)
    rw [fzero]
    -- have refxnonneg := fxnonneg
    -- rw [← fxisreal] at refxnonneg
    -- have zisz : (0 : ℂ) = (0 : ℝ) := by exact rfl
    -- rw [zisz, ← fxisreal] at fxnonneg
    -- rw [← fxisreal, ← fyisreal]
    simp
    have fxim0 : (f (x * star x)).im = (0 : ℝ) := by exact fOfxStarxHas0Im f x
    have fyim0 : (f (y * star y)).im = (0 : ℝ) := by exact fOfxStarxHas0Im f y
    have fximeqfyim := fxim0
    rw [← fyim0] at fximeqfyim
    #check Complex.le_def.mp fxnonneg
    have : (0 : ℂ).re ≤ (f (x * star x)).re := by sorry
    sorry
  sorry


-- Begin code from Eric Wieser
-- noncomputability should be fixed in by Eric Wieser's bug fix
noncomputable def mySesquilinear (f : A →ₚ[ℂ] ℂ) : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ A).comp (starLinearEquiv ℂ (A := A) : A →ₗ⋆[ℂ] A) |>.compr₂ₛₗ f

@[simp]
theorem mySesquilinear_apply (f : A →ₚ[ℂ] ℂ) (x y : A) :
  mySesquilinear f x y = f (star x * y) := rfl
-- End code from Eric Wieser

lemma add_mem_helper (f : A →ₚ[ℂ] ℂ) (a b : A) : a ∈ {a | f (star a * a) = 0}
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

lemma myCS (f : A →ₚ[ℂ] ℂ) (a b : A) :
  norm (f (star b * a)) ^ 2 ≤ f (star b * b) * f (star a * a) := by
  rw [← mySesquilinear_apply f a a, ← mySesquilinear_apply f b b, ← mySesquilinear_apply f b a]
  sorry

lemma smul_mem_helper (f : A →ₚ[ℂ] ℂ) (b : A) {a : A} : a ∈ {a | f (star a * a) = 0}
  → b • a ∈ {a | f (star a * a) = 0} := by
  rw [Set.mem_setOf, Set.mem_setOf]
  intro h
  #check mySesquilinear_apply f a a
  rw [← mySesquilinear_apply f a a] at h
  rw [← mySesquilinear_apply f (b • a) (b • a)]
  sorry

-- From Aupetit leamm 6.2.18
-- should probably use module ideal? see 10.1.1 MIL
def N (f : A →ₚ[ℂ] ℂ) : Ideal A where
  carrier := {a : A | f (star a * a) = 0}
  add_mem' := by intro a b; exact add_mem_helper f a b
  zero_mem' := by simp;
  smul_mem' := by intro b; exact smul_mem_helper f b

--theorem aupetit6_2_18_closed : IsClosed {a : A | f (star a * a) = 0} := by sorry
variable (f : A →ₚ[ℂ] ℂ)
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
