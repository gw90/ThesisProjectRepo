import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Algebra.Order.Module.PositiveLinearMap
-- Mathlib.Algebra.Star.StarRingHom
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

example {a b : ℚ} (h1 : a ≤ 1) (h2 : b ≤ 3) : (a + b) / 2 ≤ 2 := by
  linear_combination (h1 + h2) / 2

open ComplexConjugate
open scoped ComplexOrder
scoped[ComplexOrder] attribute [instance] Complex.partialOrder -- this is very important
open Complex
open Mathlib.Tactic.LinearCombination

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)
-- LinearMap (starRingEnd R) M M₂
variable (p : A) (q : A) -- for experimentation. remove later
set_option linter.unusedSectionVars false -- remove this at the end

/-def myf (f : A →ₚ[ℂ] ℂ) : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ A).comp (starLinearEquiv ℂ (A := A) : A →ₗ⋆[ℂ] A) |>.compr₂ₛₗ f
-/
lemma aupetit_6_2_15lemma (x y : A) (l : ℂ) :
  0 ≤ f (x * star x) + l * f (y * star x) + (conj l) * f (x * star y)
    + l * (conj l) * f (y * star y) := by
  have hnonneg :=  PositiveLinearMap.map_nonneg f (mul_star_self_nonneg (x + (l • y)))
  rw [add_mul, star_add, mul_add, mul_add] at hnonneg
  simp only [star_smul, RCLike.star_def, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, map_add,
    map_smul, smul_eq_mul] at hnonneg
  have h : f (x * star x) + (starRingEnd ℂ) l * f (x * star y)
      + (l * f (y * star x) + (starRingEnd ℂ) l * (l * f (y * star y)))
    = f (x * star x) + l * f (y * star x) + (starRingEnd ℂ) l * f (x * star y)
      + l * (starRingEnd ℂ) l * f (y * star y) := by ring
  rw [← h]
  assumption

-- instance {F : Type*} [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂] [OrderHomClass F A₁ A₂] :
--    StarHomClass F A₁ A₂
-- should give:
open PositiveLinearMap
theorem aupetit_6_2_15i (x : A) : f (star x) = conj (f x) := by simp [map_star]

lemma fOfxStarxIsReal (x : A) : (f (x * star x)).re = f (x * star x) := by
  have xstarmul : star (x * star x) = x * star x := by exact star_mul_star x x
  have fstareqfnostar : f (star (x * star x)) = f (x * star x)
    := by exact congrArg (⇑f) xstarmul
  have fstareqconj: f (star (x * star x)) = conj (f (x * star x))
    := by exact aupetit_6_2_15i f (x * star x)
  rw [fstareqconj] at fstareqfnostar
  have fxisreal := Complex.conj_eq_iff_re.mp fstareqfnostar
  exact fxisreal

lemma fxx_eq_conj (x : A) : conj (f (x * star x)) = f (x * star x) :=
  conj_eq_iff_re.mpr (fOfxStarxIsReal f x)

lemma fOfxStarxHas0Im (x : A) : (f (x * star x)).im = 0 := by
  have xstarmul : star (x * star x) = x * star x := by exact star_mul_star x x
  have fstareqfnostar : f (star (x * star x)) = f (x * star x)
    := by exact congrArg (⇑f) xstarmul
  have fstareqconj: f (star (x * star x)) = conj (f (x * star x))
    := by exact aupetit_6_2_15i f (x * star x)
  rw [fstareqconj] at fstareqfnostar
  have fxisreal := Complex.conj_eq_iff_im.mp fstareqfnostar
  exact fxisreal

example (c : ℂ) : norm c ^ 2 = c * conj c := by exact Eq.symm (mul_conj' c)

lemma aupetit_6_2_15iilemma (t : ℂ) (ht : t = conj t) (x y : A) (h : f (x * star y) ≠ 0) :
  -- initally did the proof with (t : ℝ), but then when I changed it, it immediately hilighted
  -- the step that failed, so I could go, rigirously repair the proof step by step
  -- TO-DO: re-write with a calculation proof
  0 ≤ f (x * star x) + 2 * t * norm (f (x * star y)) + t^2 * f (y * star y) := by
  have := aupetit_6_2_15lemma f x y ((t * f (x * star y))/(norm (f (x * star y))))
  have fact := mul_conj' (f (x * star y))
  have fact2 : f (y * star x) = f (star (x * star y)) := by simp
  have fact3 : f (star (x * star y)) = conj (f (x * star y)) := aupetit_6_2_15i (f) (x * star y)
  have fact4 : f (y * star x) = conj (f (x * star y)) := Eq.trans fact2 fact3
  simp [fact4] at this
  have fact5 : ↑t * f (x * star y) / ↑‖f (x * star y)‖ * (starRingEnd ℂ) (f (x * star y)) =
    ↑t * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))) / ↑‖f (x * star y)‖ := by field_simp
  simp [fact] at fact5
  have fact6 : (t : ℂ) * ↑‖f (x * star y)‖ ^ 2 / ↑‖f (x * star y)‖ = ↑t * ↑‖f (x * star y)‖ := by
    field_simp
  have fact7 :=  Eq.trans fact5 fact6
  simp [fact7] at this
  have fact8 : ↑t * (starRingEnd ℂ) (f (x * star y)) / ↑‖f (x * star y)‖ * f (x * star y) =
    ↑t * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))) / ↑‖f (x * star y)‖ := by ring
  simp [fact] at fact8
  have fact9 : (t : ℂ) * ↑‖f (x * star y)‖ ^ 2 / ↑‖f (x * star y)‖ = ↑t * ↑‖f (x * star y)‖ := by
    field_simp
  have fact10 := Eq.trans fact8 fact9
  rw [ht] at this
  simp [fact10] at this
  have fact11 :
    ↑t * f (x * star y) / ↑‖f (x * star y)‖ *
      (↑t * (starRingEnd ℂ) (f (x * star y)) / ↑‖f (x * star y)‖) *
      f (y * star y) =
      (↑t^2 * (f (x * star y) * (starRingEnd ℂ) (f (x * star y))))/ ↑‖f (x * star y)‖ ^ 2 *
      f (y * star y) := by field_simp
  rw [← ht] at this
  rw [fact11] at this
  simp [fact] at this
  field_simp at this
  nth_rw 2 [add_assoc] at this
  rw [← two_mul, ← mul_assoc] at this
  exact this

theorem aupetit_6_2_15ii (x y : A) :
  norm (f (x * star y)) ^ 2 ≤ f (x * star x) * f (y * star y) := by
  have fxisreal := fOfxStarxIsReal f x
  have fyisreal := fOfxStarxIsReal f y
  have fxx := fxx_eq_conj f x
  have fyy := fxx_eq_conj f y
  have fxnonneg := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg x)
  have fynonneg := PositiveLinearMap.map_nonneg f (mul_star_self_nonneg y)
  have fyyIm0: (f (y * star y)).im  = 0 := by exact fOfxStarxHas0Im f y
  have fxxIm0: (f (x * star x)).im  = 0 := by exact fOfxStarxHas0Im f x
  have fxxEqConj: f (x * star x)  = conj (f (x * star x)) := by exact id (Eq.symm fxx)

  have normIm0 : (norm (f (x * star y)) :ℂ ).im = 0 := by exact rfl
  have fullProdIm0 := Complex.smul_im (-‖f (x * star y)‖) (f (y * star y))⁻¹

  have invIm0 : ((f (y * star y))⁻¹).im = 0 := by
    simp [Complex.inv_im]
    left
    exact fyyIm0

  rw [invIm0, MulActionWithZero.smul_zero (-‖f (x * star y)‖)] at fullProdIm0
  have eqOwnConj : (- ‖f (x * star y)‖ • (f (y * star y))⁻¹)
   = conj (- ‖f (x * star y)‖ • (f (y * star y))⁻¹) :=
     Eq.symm ((fun {z} ↦ conj_eq_iff_im.mpr) fullProdIm0)

  have inter := aupetit_6_2_15iilemma (f)
    (-‖f (x * star y)‖ • (f (y * star y))⁻¹) eqOwnConj x y

  by_cases fzero : f (x * star y) = 0
  · simp only [fzero, norm_zero, ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ge_iff_le]
    exact Left.mul_nonneg fxnonneg fynonneg
  have fzero2 := fzero
  by_cases fyyzero : f (y * star y) = 0
  · push_neg at fzero2
    have twoEqConj : 2 = conj (2 : ℂ) := by exact Eq.symm ((fun {z} ↦ conj_eq_iff_re.mpr) rfl)
    by_cases fxzero : f (x * star x) = 0
    · have halfEqOwnConj : (-1/2 : ℂ) = conj (-1/2 : ℂ) := by simp; congr;
      have l1 := aupetit_6_2_15iilemma (f) (-1/2) halfEqOwnConj x y fzero2
      rw [fxzero, fyyzero] at l1
      have step : (0 : ℂ) ≤ - norm (f (x * star y)) := by
        calc
          (0 : ℂ) ≤ 0 + 2 * (- 1 / 2) * ↑‖f (x * star y)‖ + (- 1 / 2) ^ 2 * 0 := l1
          _ = - ↑‖f (x * star y)‖ := by simp; norm_num
      rw [fxzero, fyyzero, zero_mul]
      have normLeq0 : (norm (f (x * star y)) : ℂ) ≤ 0 := by exact neg_nonneg.mp step
      have := norm_nonneg (f (x * star y))
      have normGeq0 : 0 ≤ (norm (f (x * star y)) : ℂ) := by exact zero_le_real.mpr this
      have norm0 : 0 = (norm (f (x * star y)) : ℂ) := le_antisymm normGeq0 normLeq0
      rw [← norm0]
      simp
    let c := (2 * f (x * star x))/(-2 * norm (f (x * star y)))

    have constEqOwnConj : c = conj c := by
      dsimp [c]
      simp only [neg_mul, map_div₀, map_mul, map_neg, conj_ofReal]
      rw [← fxxEqConj, ← twoEqConj]
    have := aupetit_6_2_15iilemma (f) c constEqOwnConj x y fzero2
    rw [fyyzero, mul_zero, add_zero] at this
    dsimp [c] at this
    field_simp at this
    norm_num at this
    have fxneg : f (x * star x) < 0 := by exact lt_of_le_of_ne this fxzero
    linarith
  push_neg at fzero

  have h := inter fzero
  simp at h
  rw [add_assoc, add_comm] at h
  have step1 := tsub_le_iff_right.mpr h


  rw [zero_sub] at step1

  have step2 := by calc
    -f (x * star x) ≤
    -(2 * (‖f (x * star y)‖ / (f (y * star y))) * ↑‖f (x * star y)‖) +
    (‖f (x * star y)‖ / (f (y * star y))) ^ 2 * f (y * star y) := step1
    _ = -(2 * (‖f (x * star y)‖^2 / (f (y * star y)))) +
    ((‖f (x * star y)‖^2) / ((f (y * star y)))) * (1/(f (y * star y))) * f (y * star y) := by ring
    _ = -(2 * (‖f (x * star y)‖^2 / (f (y * star y)))) +
    ((‖f (x * star y)‖^2) / ((f (y * star y)))) := by field_simp
    _ = (-(2 * (‖f (x * star y)‖^2)) +
    ((‖f (x * star y)‖^2))) * ((f (y * star y)))⁻¹ := by ring

  have step3 : -f (x * star x) * (f (y * star y)) ≤
  (-(2 * (‖f (x * star y)‖^2)) +
    ((‖f (x * star y)‖^2))) * ((f (y * star y)))⁻¹ * (f (y * star y)) :=
      mul_le_mul_of_nonneg_right step2 fynonneg

  rw [mul_assoc] at step3
  nth_rw 4 [mul_comm] at step3
  rw [Complex.mul_inv_cancel fyyzero, mul_one] at step3
  have step4 := by calc
    -f (x * star x) * f (y * star y) ≤
      -(2 * ↑‖f (x * star y)‖ ^ 2) + ↑‖f (x * star y)‖ ^ 2 := step3
    _ = (-2 + 1) * ↑‖f (x * star y)‖ ^ 2 := by ring
    _ = -1 * ↑‖f (x * star y)‖ ^ 2 := by norm_num

  have step5 := neg_le_neg step4
  simp at step5
  exact step5

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
  have : f (star (a + b) * (a + b)) = f ((star a + star b) * (a + b)) := by simp
  have : 0 ≤ star (a + b) * (a + b) := by exact star_mul_self_nonneg (a+b)
  have : 0 ≤ f (star (a + b) * (a + b)) := by exact PositiveLinearMap.map_nonneg f this

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

/-
Graveyard:

    -- have refxnonneg := fxnonneg
    -- rw [← fxisreal] at refxnonneg
    -- have zisz : (0 : ℂ) = (0 : ℝ) := by exact rfl
    -- rw [zisz, ← fxisreal] at fxnonneg
    -- rw [← fxisreal, ← fyisreal]

    -- have fxim0 : (f (x * star x)).im = (0 : ℝ) := by exact fOfxStarxHas0Im f x
    -- have fyim0 : (f (y * star y)).im = (0 : ℝ) := by exact fOfxStarxHas0Im f y
    -- have fximeqfyim := fxim0
    -- rw [← fyim0] at fximeqfyim
    -- #check Complex.le_def.mp fxnonneg
 wlog fyyzero : f (y * star y) ≠ 0 generalizing x y with H
  . push_neg at fyyzero
    have rev := H y x

    have := by calc
     ‖f (x * star y)‖ = ‖conj (f (x * star y))‖ := Eq.symm (norm_conj (f (x * star y)))
     _ = ‖f (star (x * star y))‖ := by rw [aupetit_6_2_15i (f) (x * star y)]
     _ = ‖f (y * star x)‖ := by simp
    rw [this, mul_comm]
    #check (LinearMap.inl_map_mul x y)
    #check LinearMap.inl_map_mul
    #check (f.toLinearMap)
    #check
    apply rev
    sorry


  -- by_cases fyyzero : f (y * star y) = 0
  -- · rw [fyyzero, mul_zero]
  --   have fofyyzero := fyyzero
  --   have inter := (LinearMap.map_smul (f.toLinearMap) 0 y)

  --   have zisz : 0 = HSMul.hSMul 0 (f.toLinearMap y) := by ring
  --   norm_cast at zisz
  --   rw [zisz] at fyyzero
  --   norm_cast at inter
  --   rw [← inter] at fyyzero
  --   have eqLine : f (y * star y) = f.toLinearMap (y * star y) := by exact rfl
  --   rw [eqLine] at fyyzero

  --   have : f = f.toLinearMap := by exact rfl
  --   rw [← this] at fyyzero
  --   norm_cast
  --   apply (sq_nonpos_iff (‖f (x * star y)‖)).mpr
  --   rw [norm_eq_zero]
  --   have zerobothtimes: 0 • y = y * (0 : A) := by simp
  --   have eq0self : f (y * star y) = f (0 • y) := by exact fyyzero
  --   rw [zerobothtimes] at eq0self

  --   by_cases finj : Function.Injective f
  --   . have yyzero : y * star y = 0 • y := finj fyyzero
  --     simp at yyzero
  --     rw [yyzero]
  --     simp
  --   --rw [← (LinearMap.map_zero f.toLinearMap)] at fyyzero

  --   #check congrFun

  --   sorry
  -- push_neg at fyyzero

  have eqOwnConj2 : -↑‖f (x * star y)‖ = (starRingEnd ℂ) (-↑‖f (x * star y)‖) := by simp [(Complex.conj_ofReal (- norm (f (x * star y)))).symm]
    have inter2 := (aupetit_6_2_15iilemma (f) (- norm (f (x * star y))) (eqOwnConj2)) y x
    have := by calc
      conj (f (x * star y)) = f (star (x * star y)) := Eq.symm (aupetit_6_2_15i f (x * star y))
      _ = f (y * star x) := by simp
    have fxsynonzero : f (y * star x) ≠ 0 := by
      rw [← this]
      by_contra c
      . simp at c
        exact fzero c
    have h2 := inter2 fxsynonzero
    rw [fyyzero, zero_add] at h2
    have := by calc
      norm (f (y * star x)) = norm (conj (f (y * star x))) := by simp
      _ = norm (f (star (y * star x))) := by congr; exact Eq.symm (aupetit_6_2_15i f (y * star x))
      _ = norm (f (x * star y)) := by simp
    rw [this, pow_two] at h2
    have := by calc
      2 * -↑‖f (x * star y)‖ * ↑‖f (x * star y)‖ + -↑‖f (x * star y)‖ * -↑‖f (x * star y)‖ * f (x * star x)
      = 2 * -↑‖f (x * star y)‖ ^ 2 + (-↑‖f (x * star y)‖) ^ 2 * f (x * star x) := by ring
      _ = 2 * -↑‖f (x * star y)‖ ^ 2 + ↑‖f (x * star y)‖ ^ 2 * f (x * star x) := by simp
      _ = -2 * ↑‖f (x * star y)‖ ^ 2 + ↑‖f (x * star y)‖ ^ 2 * f (x * star x) := by simp
      _ = ↑‖f (x * star y)‖ ^ 2 *(-2 + f (x * star x)) := by ring
      _ = -↑‖f (x * star y)‖ ^ 2 *(2 - f (x * star x)) := by ring
    rw [this] at h2
    -- break into cases where 2-f(xx*)≤0 and where >0

    lemma aupetit_6_2_15iilemma' (t : ℂ) (ht : t = conj t) (x y : A) (h : f (x * star y) ≠ 0) :
  -- initally did the proof with (t : ℝ), but then when I changed it, it immediately hilighted
  -- the step that failed, so I could go, rigirously repair the proof step by step
  -- TO-DO: re-write with a calculation proof
  - (2 * t * norm (f (x * star y)) + t^2 * f (y * star y)) ≤ f (x * star x) := by
    have l1 := aupetit_6_2_15iilemma (f) t (ht) x y h

    have interStep := (tsub_le_iff_right (a := 0) (b := (2 * t * norm (f (x * star y)) + t^2 * f (y * star y))) (c := f (x * star x))).mpr
    norm_cast at interStep
    norm_cast at l1
    rw [add_assoc] at l1
    have interStep2 := interStep l1
    rw [zero_sub] at interStep2
    have interStep3 := neg_le.mp interStep2

have negOneEqOwnConj : (-1 : ℂ) = conj (-1 : ℂ) := by rw [map_neg, map_one]
    push_neg at fzero2
    have := by calc
      conj (f (x * star y)) = f (star (x * star y)) :=
        Eq.symm (aupetit_6_2_15i f (x * star y))
      _ = f (y * star x) := by simp
    have : conj (f (y * star x)) = conj (conj (f (x * star y))) := by
      congr
      exact this.symm
    simp at this
    rw [← this] at fzero2
    rw [ne_eq, map_eq_zero] at fzero2
    push_neg at fzero2
    have eq1 := aupetit_6_2_15iilemma (f) (-1) negOneEqOwnConj y x fzero2
    rw [fyyzero] at eq1
    simp only [mul_neg, mul_one, neg_mul, zero_add, even_two, Even.neg_pow, one_pow, one_mul,
      add_zero] at eq1
    have oneEqOwnConj : (1 : ℂ) = conj (1 : ℂ) := by rw [map_one]
    have eq2 := aupetit_6_2_15iilemma (f) (1) oneEqOwnConj y x fzero2
    rw [fyyzero] at eq2
    simp at eq2
    have : 0 ≤ -(2 * ↑‖f (y * star x)‖) + f (x * star x) - (2 * ↑‖f (y * star x)‖ + f (x * star x)) := by
      linear_combination (eq1 - eq2)
      -- le_neg_add_iff_add_le

    sorry
-/
