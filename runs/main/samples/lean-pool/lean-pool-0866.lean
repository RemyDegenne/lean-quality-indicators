@[expose] public section

open MeasureTheory Measure Metric Filter Set Topology

open scoped NNReal ENNReal MeasureTheory

noncomputable section

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

lemma measure_integralDensitySetAbove_eq_zero
    {μ : Measure X} [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    (hμ : IsRadon μ)
    {f : X → ℝ} (hf : LocallyIntegrable f μ)
    {s : ℝ} (hs : 0 ≤ s)
    (hdim : ∀ᵐ x ∂μ,
      Tendsto (fun r => μ (closedBall x r) / ENNReal.ofReal (r ^ s))
        (𝓝[>] (0 : ℝ)) (𝓝 0))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    μ {x | ε < integralDensityLimsup μ f s x} = 0 := by
  refine MeasureTheory.measure_mono_null ?_
    (measure_integralDensitySet_eq_zero hμ hf hs hdim)
  exact fun x hx => lt_trans hε hx

end
end
