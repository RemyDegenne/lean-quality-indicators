public section

noncomputable section

open Set Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Lift flat coordinates to the nonnegative orthant boundary by minimum subtraction. -/
def coordinateSimplexBoundaryLift (y : ι → ℝ) : Option ι → ℝ :=
  Option.elim' (orthantLift y).2 (orthantLift y).1

end TauCeti
end
end
