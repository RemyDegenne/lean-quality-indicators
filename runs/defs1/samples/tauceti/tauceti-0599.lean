public noncomputable section

open MeasureTheory

open scoped Pointwise Topology

namespace TauCeti

variable (ι : Type*) [Fintype ι]

/-- The closed ℓ¹ unit ball in a finite real coordinate space. -/
def l1Ball : Set (ι → ℝ) := {x | ∑ i, |x i| ≤ 1}

end TauCeti
end
