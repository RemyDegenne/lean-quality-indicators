public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

namespace Division

variable {d : Coordinate} {D : Set ℂ}

theorem integrableOn_iff (V : Division d D) {f : ℂ → ℝ} :
    IntegrableOn f D ↔ ∀ K ∈ V.cells, IntegrableOn f (K.region d) := by
  conv_lhs => rw [← V.covers]
  exact integrableOn_finset_iUnion

end Division
end TauCeti.Green
end
end
