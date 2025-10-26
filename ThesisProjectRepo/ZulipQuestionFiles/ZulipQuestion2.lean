import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

open ComplexConjugate
open scoped ComplexOrder
open scoped CStarAlgebra
scoped[ComplexOrder] attribute [instance] Complex.partialOrder
scoped[CStarAlgebra] attribute [instance] CStarAlgebra.spectralOrder

variable {A : Type*} [CStarAlgebra A]
variable (f : A →ₚ[ℂ] ℂ)
example (x : A) : f (star x) = conj (f x) := by sorry


example (x : A) : f (star x) = (starRingEnd ℂ) (f x) := by sorry
