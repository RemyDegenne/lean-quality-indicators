public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure Set Filter Metric Module

open scoped Topology ENNReal Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → EReal}

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable (μ : Measure E) {ν : Measure E} [ν.IsAddHaarMeasure]

omit μ in
theorem mongeAmpereMeasure_add {μ₁ μ₂ : Measure E} (hμ₁ : μ₁ ≪ ν) (hμ₂ : μ₂ ≪ ν) :
    mongeAmpereMeasure (μ₁ + μ₂) f = mongeAmpereMeasure μ₁ f + mongeAmpereMeasure μ₂ f := by
  by_cases hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}
  · by_cases hbot : ∀ x, f x ≠ ⊥
    · ext s hs
      rw [add_apply, mongeAmpereMeasure_apply _ hf hbot (hμ₁.add_left hμ₂) hs,
        mongeAmpereMeasure_apply _ hf hbot hμ₁ hs, mongeAmpereMeasure_apply _ hf hbot hμ₂ hs,
        add_apply]
    · obtain ⟨x, hx⟩ := not_forall_not.1 hbot
      simp only [mongeAmpereMeasure_eq_zero_of_eq_bot _ hx, add_zero]
  · simp only [mongeAmpereMeasure_eq_zero_of_not_convex _ hf, add_zero]

end TauCeti
end
end
