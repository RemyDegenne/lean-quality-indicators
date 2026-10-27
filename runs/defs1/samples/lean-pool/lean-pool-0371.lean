@[expose] public section

open scoped InnerProductSpace ENNReal CompactlySupported

open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti

namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {a : H →L[ℂ] H}

section Projections

variable (ha : IsStarNormal a) {κ : spectrum ℂ a → ℝ} (hκ : Measurable κ)

/-- The relabelled diagonal measure. -/
-- `@[expose]` for the same reason as `toProjValMeasure`, whose exposed body references
-- this one. Recorded debt, not an endorsement.
noncomputable def specDiag (κ' : spectrum ℂ a → ℝ) (ξ : H) : Measure ℝ :=
  Measure.map κ' (diagMeasure ha ξ)

end Projections
end BorelCalculus
end TauCeti
end
