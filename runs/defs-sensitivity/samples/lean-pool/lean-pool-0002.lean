@[expose] public section

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

namespace VML

/-- Squared Euclidean norm: ‖z‖² = z · z = ∑ᵢ zᵢ² -/
def normSq (z : Fin 3 → ℝ) : ℝ := dotProduct z z

end VML
end
end
