namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem realNormalizedFirstCoefficientMap_ker :
    LinearMap.ker (F.realNormalizedFirstCoefficientMap w) =
      LinearMap.ker (F.realReducedRelativeSquareSymbolMap w hw) := by
  have hk : LinearMap.ker ((F.normalizedFirstCoefficientMap w).baseChange ℝ) =
      LinearMap.ker ((F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ) := by
    rw [← realification_ker, ← realification_ker, F.normalizedFirstCoefficientMap_ker w hw]
  ext x
  change F.firstCoefficientRealEquiv w ((F.normalizedFirstCoefficientMap w).baseChange ℝ x) = 0 ↔
    (F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ x = 0
  rw [LinearEquiv.map_eq_zero_iff]
  exact SetLike.ext_iff.mp hk x

end Erdos3.NilpotentLieFiltration
end
end OAI
