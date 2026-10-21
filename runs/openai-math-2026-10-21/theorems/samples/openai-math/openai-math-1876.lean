namespace OAI

section

namespace Erdos3

open Module

open scoped Matrix TensorProduct NNReal

variable {L ι μ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype ι] [Fintype μ] {V : Submodule ℚ L}

theorem realQuotientCoordinateMap_grid (b : Basis μ ℚ L) (f : Basis ι ℚ (L ⧸ V))
    (l : ℕ) (x : ℝ ⊗[ℚ] L) (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    realQuotientCoordinateMap f x ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
  rw [realQuotientCoordinateMap_eq_matrix b f x]
  exact real_matrix_denominator_grid (quotientCoordinateMatrix b f) l _ hx

end Erdos3
end
end OAI
