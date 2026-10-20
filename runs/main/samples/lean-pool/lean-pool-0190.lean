@[expose] public section

open Complex MeasureTheory Real Finset

open scoped BigOperators Topology

noncomputable section

namespace HermitekLEAN

theorem hermiteCoeff_expansion :
    ∀ {k : ℕ} {G : ℂ → ℂ}, G ∈ Hk k → G = hermiteSeries k (hermiteCoeff k G) := by
  intro k G hG
  ext z
  exact ((hG.2 z).tsum_eq).symm

end HermitekLEAN
end
end
