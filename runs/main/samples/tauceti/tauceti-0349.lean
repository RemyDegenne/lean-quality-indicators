public section

noncomputable section

open MeasureTheory Measure Set Filter ProbabilityTheory

open scoped Topology Gradient ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure] {μ ν : Measure E}
  {f : E → EReal}

theorem mongeAmpereMeasure_eq_withDensity_inv_iff (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {g : E → ℝ≥0∞} (hg : Measurable g) (hgtop : ∀ᵐ y ∂ρ, g y ≠ ⊤)
    {T : E → E} (hT : HasLaw T (ρ.withDensity g) μ) (hD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    (hsub : ∀ᵐ x ∂μ, T x ∈ subdifferential (innerₗ E) f x) :
    mongeAmpereMeasure ρ f = μ.withDensity (fun x => (g (T x))⁻¹) ↔
      ρ (subgradientImage (innerₗ E) f (interior {x | f x ≠ ⊤}) ∩ {y | g y = 0}) = 0 := by
  have hZ : MeasurableSet {y | g y = 0} := hg (measurableSet_singleton 0)
  have hsing : mongeAmpereMeasure (ρ.restrict {y | g y = 0}) f univ =
      ρ (subgradientImage (innerₗ E) f (interior {x | f x ≠ ⊤}) ∩ {y | g y = 0}) := by
    rw [mongeAmpereMeasure_apply _ hf hbot (absolutelyContinuous_of_le restrict_le_self)
      MeasurableSet.univ, univ_inter, restrict_apply' hZ]
  have hσ := sigmaFinite_mongeAmpereMeasure ρ f
  have hsplit := mongeAmpereMeasure_eq_withDensity_inv_add hf hbot hg hgtop hT hD hsub
  rw [← hsing, measure_univ_eq_zero]
  refine ⟨fun h => ?_, fun h => by rw [hsplit, h, add_zero]⟩
  -- `MA_f` is σ-finite, so the absolutely continuous part can be cancelled.
  have : SigmaFinite (μ.withDensity fun x => (g (T x))⁻¹) := by rw [← h]; exact hσ
  exact (Measure.add_right_inj _ _ 0).1 (hsplit.symm.trans (h.trans (add_zero _).symm))

end TauCeti
end
end
