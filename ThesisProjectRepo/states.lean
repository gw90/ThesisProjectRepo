import Mathlib.Algebra.DirectSum.Basic
import ThesisProjectRepo.AguilarMorphisms

open ComplexConjugate
open scoped ComplexOrder
open Complex

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

@[ext]
structure state where
  functional : A →ₚ[ℂ] ℂ
  of_one_eq_one : functional 1 = 1

#check state.of_one_eq_one
#check state.functional

open DirectSum

open GNS
def BigH := ⨁ state, GNS.H state (A := A)

#check BigH

variable (s : state (A := A))
#check s.functional
#check ⨁ state, GNS.H state (A := A)

