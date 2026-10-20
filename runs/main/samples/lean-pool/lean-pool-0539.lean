@[expose] public section

namespace Stafford38.WeylEulerRemainder

open Polynomial

open Stafford

open AlgebraicAnalysis

open AlgebraicAnalysis.OreDivision

open AlgebraicAnalysis.OreAssociativity

open Stafford38.OreCoordinateStage

open Stafford38.OrePairStage

open Stafford38.WeylEulerSubring

open Stafford38.WeylEulerResidue

open Stafford38.EulerSurjectivity

noncomputable section

variable (B : Type*) [Ring B] [Algebra ℚ B]

local instance : Algebra ℚ (CoordinateStage (B := B)) :=
  coordinateStageAlgebra

local instance : Algebra ℚ (PairStage (B := B)) :=
  pairStageAlgebra

theorem normalForm_sub_X_pow_hasPositiveCoordinateFactor
    (H : Polynomial (CoordinateStage (B := B))) (N : ℕ)
    (hN : H.coeff N = 1)
    (hgt : ∀ j, N < j → H.coeff j = 0) :
    HasPositiveCoordinateFactor B N
      (normalForm (coordinateDerivation (B := B))
        (H - Polynomial.X ^ N)) := by
  apply hasPositiveCoordinateFactor_of_outer_support B
  intro j hj
  change j ∈ ((normalFormAddEquiv (coordinateDerivation (B := B))).symm
    ((normalFormAddEquiv (coordinateDerivation (B := B)))
      (H - Polynomial.X ^ N))).support at hj
  rw [(normalFormAddEquiv (coordinateDerivation (B := B))).symm_apply_apply] at hj
  exact support_sub_X_pow_lt B H N hN hgt j hj

end
end Stafford38.WeylEulerRemainder
end
