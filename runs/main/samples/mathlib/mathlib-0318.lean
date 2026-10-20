public section

open Filter

open scoped ENNReal NNReal MeasureTheory Topology

namespace MeasureTheory

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}

section WithDensity

variable {m : MeasurableSpace α} {μ : Measure α}

theorem withDensity_eq_iff {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) :
    μ.withDensity f = μ.withDensity g ↔ f =ᵐ[μ] g :=
  ⟨fun hfg ↦ by
    refine AEMeasurable.ae_eq_of_forall_setLIntegral_eq hf hg hfi ?_ fun s hs _ ↦ ?_
    · rwa [← setLIntegral_univ, ← withDensity_apply g MeasurableSet.univ, ← hfg,
        withDensity_apply f MeasurableSet.univ, setLIntegral_univ]
    · rw [← withDensity_apply f hs, ← withDensity_apply g hs, ← hfg], withDensity_congr_ae⟩

end WithDensity
end MeasureTheory
end
