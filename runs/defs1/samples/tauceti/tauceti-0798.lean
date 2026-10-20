public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure Set Filter Metric Module

open scoped Topology ENNReal Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → EReal}

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open Classical in
/-- The **Aleksandrov Monge–Ampère measure** of `f : E → EReal` with respect to a measure `μ`
that is absolutely continuous with respect to an additive Haar measure. When `f` is convex
(convex real epigraph, never `⊥`), it is the measure with `MA_f(s) = μ(∂f(s ∩ D))` for
measurable `s`, where `D` is the interior of the effective domain and `∂f` the subgradient image
for the inner product (`mongeAmpereMeasure_apply`). For an additive Haar `μ` this is the
Aleksandrov measure; for `μ = ν.withDensity g` it is the weighted measure `∫_{∂f(s ∩ D)} g dν`.
If `f` is not convex, or `μ` is not absolutely continuous with respect to a Haar measure, it is
`0`. -/
def mongeAmpereMeasure (μ : Measure E) (f : E → EReal) : Measure E :=
  if h : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2} ∧ (∀ x, f x ≠ ⊥) ∧
      ∃ ν : Measure E, ν.IsAddHaarMeasure ∧ μ ≪ ν then
    Measure.ofMeasurable
      (fun s _ => μ (subgradientImage (innerₗ E) f (s ∩ interior {x | f x ≠ ⊤})))
      (by simp) fun g hg hd => by
        obtain ⟨hf, hbot, ν, _, hμ⟩ := h
        simp only [iUnion_inter, subgradientImage_iUnion]
        exact measure_iUnion₀
          (fun i j hij => hμ (aedisjoint_subgradientImage ν f
            ((hd hij).mono inter_subset_left inter_subset_left)))
          fun i => (nullMeasurableSet_subgradientImage hf hbot ν (hg i)).mono_ac hμ
  else 0

end TauCeti
end
end
