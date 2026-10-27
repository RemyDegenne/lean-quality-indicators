public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

/-- **Equal measures give isometrically identical `Lp` spaces.** This is `cast` along the equality
of types `↥(Lp E p μ) = ↥(Lp E p ν)`, packaged as a linear isometric equivalence so that it can be
composed with other isometries; `TauCeti.coeFn_castLpₗᵢ` records that it still does not move
representatives. -/
noncomputable def castLpₗᵢ {α E 𝕜 : Type*} [MeasurableSpace α] [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ ν : Measure α}
    (h : μ = ν) : Lp E p μ ≃ₗᵢ[𝕜] Lp E p ν :=
  h.rec (motive := fun m _ => Lp E p μ ≃ₗᵢ[𝕜] Lp E p m) (LinearIsometryEquiv.refl 𝕜 _)

end TauCeti
end
