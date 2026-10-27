public section

open Set

open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → ℝ} {K : ℝ≥0}

/-- Restrict a total Morse chain to the critical points of index `n`. -/
noncomputable def morseChainProjection (n : ℕ) : MorseChain f →ₗ[ZMod 2] MorseChainPiece f n :=
  Finsupp.lsubtypeDomain (R := ZMod 2) (M := ZMod 2)
    {p : MorseCriticalPoint f | morseIndex f p = n}

end TauCeti
end
