@[expose] public section

namespace Stafford38.WeylPBW

open Stafford

open AlgebraicAnalysis

open AlgebraicAnalysis.OreDivision

open Stafford38.Characteristic

open AlgebraicAnalysis.OreAssociativity

open Stafford38.OreCoordinateStage

open Stafford38.OreIteratedPairStage

open Stafford38.OreLinearNormalForm

open Stafford38.OrePairStage

open Stafford38.OreScalarAlgebra

open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- A free-module basis on the presented Weyl algebra, pulled back from the
standard monomial basis of the symbol polynomial space. -/
def presentedNormalFormBasis (n : Nat) :
    Module.Basis (PhaseVar n →₀ ℕ) k (PresentedWeyl k n) :=
  (MvPolynomial.basisMonomials (PhaseVar n) k).map
    (presentedNormalFormLinearEquiv k n).symm

end
end Stafford38.WeylPBW
end
