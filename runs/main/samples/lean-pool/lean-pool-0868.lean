@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Oz.OmegaOmegaBoundary

open Ordinal

open ConwayRefinement.Standalone.Oz.FinitePowerFamily

theorem boundaryConwayExponent_mem_block (n : ℕ) (p : FiniteLex n) :
    boundaryConwayExponent (toLex ⟨n, p⟩) ∈
      Set.Ioc (scale ^ (n + 1)) (scale ^ n) := by
  rw [Set.mem_Ioc, boundaryConwayExponent_apply]
  exact ⟨by
    simpa using neg_lt_neg (boundarySignedExponent_lt_blockLimit n p),
    by simpa using neg_le_neg (boundarySignedExponent_blockLowerBound n p)⟩

end ConwayRefinement.Standalone.Oz.OmegaOmegaBoundary
end
