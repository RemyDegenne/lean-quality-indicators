public section

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Topology

namespace TauCeti

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [PseudoEMetricSpace Z]
  {μ : Measure X} {ν : Measure Y} {ω ω' : X × X → Z} {ωX : X × X → Z} {ωY : Y × Y → Z}
  {p : ℝ≥0∞}

/-- The **outgoing `p`-eccentricity** of `x` about `z₀` for the measured kernel `(X, μ, ω)`: the
`Lᵖ(μ)` norm of the distance from `z₀` of the section `x' ↦ ω (x, x')`. Incoming eccentricity
is the outgoing eccentricity of `ω ∘ Prod.swap`. -/
def kernelEccentricity (p : ℝ≥0∞) (μ : Measure X) (ω : X × X → Z) (z₀ : Z) (x : X) : ℝ≥0∞ :=
  eLpNorm (fun x' ↦ edist (ω (x, x')) z₀) p μ

end TauCeti
end
end
