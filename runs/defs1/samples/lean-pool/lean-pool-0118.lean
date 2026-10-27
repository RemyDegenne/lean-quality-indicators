@[expose] public section

namespace Stafford38.CharacteristicFilteredQuotientSupport

open Stafford38.Characteristic

open Stafford38.CharacteristicFilteredQuotient

open Stafford38.CharacteristicFilteredQuotientGraded

open Stafford38.CharacteristicInitialIdeal

open Stafford38.CharacteristicInitialIdealHomogeneous

open Stafford38.EulerSurjectivity

open Stafford38.WeylFiltration

open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

variable (k : Type u) [Field k]

variable {n : ℕ}

local instance orderGradedAlgebraInstance :
    GradedAlgebra (orderDecomposition (n := n) k) :=
  MvPolynomial.weightedGradedAlgebra k (@orderWeight n)

/-- Restricting the scalar ring of an ideal does not change the underlying
additive quotient. -/
def restrictScalarsQuotientAddEquiv
    (I : RightIdeal (PresentedWeyl k n)) :
    (SymbolRing k n ⧸ (orderInitialIdeal k I).restrictScalars k) ≃+
      OrderCharacteristicModule k I where
  toEquiv := Quotient.congr (Equiv.refl _) (by
    intro P Q
    rfl)
  map_add' q r := by
    refine Quotient.inductionOn₂ q r ?_
    intro P Q
    rfl

end
end Stafford38.CharacteristicFilteredQuotientSupport
end
