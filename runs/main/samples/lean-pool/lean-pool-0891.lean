@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Topology

open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

section

section Feller

theorem mapsC0_heatSemigroup : heatSemigroup.MapsC0 := by
  intro t f
  have hrep : kernelIntegral (heatSemigroup t) f =
      fun x ↦ ∫ z, f (x + Real.sqrt t * z) ∂(gaussianReal 0 1) :=
    funext (kernelIntegral_heatSemigroup t f)
  rw [hrep]
  constructor
  · refine continuous_of_dominated (F := fun (x z : ℝ) ↦ f (x + Real.sqrt t * z))
      (bound := fun _ ↦ ‖f‖) ?_ ?_ (integrable_const (μ := gaussianReal 0 1) ‖f‖) ?_
    · exact fun x ↦ (f.continuous.comp (by fun_prop)).aestronglyMeasurable
    · exact fun x ↦ Filter.Eventually.of_forall fun z ↦ norm_apply_le_norm_c0 f _
    · exact Filter.Eventually.of_forall fun z ↦ f.continuous.comp (by fun_prop)
  · have hcg : (Filter.cocompact ℝ).IsCountablyGenerated := by
      rw [cocompact_eq_atBot_atTop]
      infer_instance
    refine Filter.tendsto_iff_seq_tendsto.mpr fun u hu ↦ ?_
    have hlim : Filter.Tendsto
        (fun n ↦ ∫ z, f (u n + Real.sqrt t * z) ∂(gaussianReal 0 1)) atTop
        (nhds (∫ _z : ℝ, (0 : ℝ) ∂(gaussianReal 0 1))) := by
      refine tendsto_integral_of_dominated_convergence
        (F := fun (n : ℕ) (z : ℝ) ↦ f (u n + Real.sqrt t * z)) (fun _ ↦ ‖f‖)
        (fun _ ↦ (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
        (integrable_const (μ := gaussianReal 0 1) ‖f‖)
        (fun _ ↦ Filter.Eventually.of_forall fun _ ↦ norm_apply_le_norm_c0 f _)
        (Filter.Eventually.of_forall fun z ↦ ?_)
      have htranslate : Filter.Tendsto (fun y : ℝ ↦ y + Real.sqrt t * z)
          (Filter.cocompact ℝ) (Filter.cocompact ℝ) :=
        CocompactMapClass.cocompact_tendsto
          ((Homeomorph.addRight (Real.sqrt t * z)).toCocompactMap)
      exact f.zero_at_infty'.comp (htranslate.comp hu)
    rw [integral_zero] at hlim
    exact hlim

end Feller
end
end MarkovProcess
end PortComputability
end
