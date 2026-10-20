@[expose] public section

open Function MeasureTheory Set

namespace QuadraticCarleson

namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction

attribute [local instance] Classical.propDecidable

/-- The source sum after its finite regrouping by parent intervals. -/
noncomputable def energyStandardRegroupedSourceAction
  (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (j : ℤ) (scale : RealInterval → ℤ) (R : Finset ℤ)
    (N : ℤ → Finset RealInterval) (x : ℝ) : ℂ :=
  ∑ I ∈ R.biUnion N, krauseLaceyLocalizedPiece 1 (j - 2) I
    (energyStandardSourceParentInput S f I₀ k₀ scale R N I) x

end KrauseLaceyBadScale
end QuadraticCarleson
end
