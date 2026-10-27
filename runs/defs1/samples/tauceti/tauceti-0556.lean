public section

noncomputable section

namespace TauCeti

open ThricePuncturedSphere Set

variable {E : Type*} [TopologicalSpace E] (p : E → ThricePuncturedSphere)

namespace FilledPoint

/-- Add a point over the puncture `1` for each component of its punctured preimage. -/
def overOne : ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne) → FilledPoint p :=
  Sum.inr ∘ Sum.inl

end FilledPoint
end TauCeti
end
end
