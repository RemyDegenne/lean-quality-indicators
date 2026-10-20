@[expose] public section

open Complex MeasureTheory Real Finset

open scoped BigOperators Topology

noncomputable section

namespace HermitekLEAN

/-- The circle defect `rhoh(w) = ||1+w| - 1|`. -/
abbrev rhoh : ℂ → ℝ := HermiteLEAN.rho

end HermitekLEAN
end
end
