@[expose] public section

namespace AlgebraicAnalysis.OreRightPBW

open Polynomial

open Module

open AlgebraicAnalysis

open AlgebraicAnalysis.OreDivision

open AlgebraicAnalysis.OreAssociativity

open AlgebraicAnalysis.OreRightQuotient

open AlgebraicAnalysis.OreDerivationRightHilbertBasis

noncomputable section

universe u

variable {B : Type u} [Ring B]

/-- The finitely supported right-coefficient combination of PBW monomials. -/
def rightPBWCombination (D : OreDivisionDerivation B) :
    (ℕ →₀ Bᵐᵒᵖ) →ₗ[Bᵐᵒᵖ] NormalOre D :=
  Finsupp.linearCombination Bᵐᵒᵖ (rightPBWMonomial D)

end
end AlgebraicAnalysis.OreRightPBW
end
