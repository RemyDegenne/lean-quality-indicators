public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric

open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {m : Measure X}

section CurvatureDimension

namespace MetricMeasureSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X] {M : MetricMeasureSpace X} {K K' : ℝ}

/-- The **curvature-dimension condition** `CD(K, ∞)` of Sturm and Lott–Villani for the
metric-measure space `M`: the reference measure has full support, and the Boltzmann entropy
relative to it is `K`-geodesically convex on the quadratic Wasserstein space `P₂(X)`. That is, any
two laws of finite second moment with `Ent_m(μᵢ) < ∞` (the entropy may be `⊥`) are joined by a
`W₂`-geodesic `(μ_t)` along which
`Ent_m(μ_t) ≤ (1 - t) Ent_m(μ₀) + t Ent_m(μ₁) - (K / 2) t (1 - t) W₂(μ₀, μ₁)²`.

The carrier is complete and separable and the reference measure is finite on bounded sets, as
`TauCeti.MetricMeasureSpace` requires. For a reference measure without full support, apply the
condition to the support reduction `TauCeti.MetricMeasureSpace.supportSpace`. -/
structure CurvatureDimensionInfinity (M : MetricMeasureSpace X) (K : ℝ) : Prop where
  /-- The reference measure has full support. -/
  support_eq_univ : M.support = univ
  /-- Any two laws of finite second moment and entropy `< ∞` are joined by a `W₂`-geodesic
  along which the entropy is `K`-convex. -/
  exists_isGeodesicSegment_convexAlong : ∀ ⦃μ₀ μ₁ : WassersteinSpace 2 X⦄,
    boltzmannEntropy M.reference ((μ₀ : ProbabilityMeasure X) : Measure X) ≠ ⊤ →
    boltzmannEntropy M.reference ((μ₁ : ProbabilityMeasure X) : Measure X) ≠ ⊤ →
    ∃ γ : ℝ → WassersteinSpace 2 X, IsGeodesicSegment γ μ₀ μ₁ ∧
      ConvexAlong K (fun μ : WassersteinSpace 2 X ↦
        boltzmannEntropy M.reference ((μ : ProbabilityMeasure X) : Measure X)) γ

end MetricMeasureSpace
end CurvatureDimension
end TauCeti
end
end
