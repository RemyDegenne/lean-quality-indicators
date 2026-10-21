namespace OAI

section

namespace Erdos3

open MeasureTheory

open scoped NNReal BigOperators

theorem retained_density_l1_comparison {W Ω X : Type*}
    [MeasurableSpace W] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure W) (ν : Measure Ω) (ξ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite ξ]
    (U V : W × Ω → X) (hU : Measurable U) (hV : Measurable V)
    (f g : W → X → ℝ) (hfm : Measurable (Function.uncurry f)) (hgm : Measurable (Function.uncurry g))
    (hf : ∀ w, (∀ x, 0 ≤ f w x) ∧ Integrable (f w) ξ ∧ (∫ x, f w x ∂ξ) = 1)
    (hg : ∀ w, (∀ x, 0 ≤ g w x) ∧ Integrable (g w) ξ ∧ (∫ x, g w x ∂ξ) = 1)
    (hUf : ∀ w, ν.map (fun a => U (w, a)) = realDensityMeasure ξ (f w))
    (hVg : ∀ w, ν.map (fun a => V (w, a)) = realDensityMeasure ξ (g w))
    {ε : ℝ} (he : ∀ φ : W × X → ℝ, Measurable φ → (∀ p, ‖φ p‖ ≤ 1) →
      |mappedTest (μ.prod ν) (fun p => (p.1, U p)) φ-
        mappedTest (μ.prod ν) (fun p => (p.1, V p)) φ| ≤ ε) :
    (∫ p, |f p.1 p.2-g p.1 p.2| ∂μ.prod ξ) ≤ ε :=
  imageComparison_density_l1 (μ.prod ν) (μ.prod ξ) _ _
    (measurable_fst.prodMk hU) (measurable_fst.prodMk hV) _ _ hfm hgm
    (densityMixture_joint_integrable μ ξ f hfm (Filter.Eventually.of_forall hf))
    (densityMixture_joint_integrable μ ξ g hgm (Filter.Eventually.of_forall hg))
    (fun p => (hf p.1).1 p.2) (fun p => (hg p.1).1 p.2)
    (retainedDensity_image_law μ ν ξ U hU f hfm hf hUf)
    (retainedDensity_image_law μ ν ξ V hV g hgm hg hVg) he

end Erdos3
end
end OAI
