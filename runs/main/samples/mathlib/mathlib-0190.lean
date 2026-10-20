@[expose] public section

open Filter Function MeasureTheory RCLike Set TopologicalSpace Topology

open scoped ENNReal NNReal Finset

variable {X Y E F : Type*}

variable {X : Type*}

section ParametricIntegral

variable {G 𝕜 : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {μ : Measure Y}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open Metric ContinuousLinearMap

theorem continuous_parametric_integral_of_continuous
    [FirstCountableTopology X] [LocallyCompactSpace X]
    [SecondCountableTopologyEither Y E] [IsLocallyFiniteMeasure μ]
    {f : X → Y → E} (hf : Continuous f.uncurry) {s : Set Y} (hs : IsCompact s) :
    Continuous (∫ y in s, f · y ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rcases exists_compact_mem_nhds x₀ with ⟨U, U_cpct, U_nhds⟩
  rcases (U_cpct.prod hs).bddAbove_image hf.norm.continuousOn with ⟨M, hM⟩
  apply continuousAt_of_dominated
  · filter_upwards with x using Continuous.aestronglyMeasurable (by fun_prop)
  · filter_upwards [U_nhds] with x x_in
    rw [ae_restrict_iff]
    · filter_upwards with t t_in using hM (mem_image_of_mem _ <| mk_mem_prod x_in t_in)
    · exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  · exact integrableOn_const hs.measure_ne_top
  · filter_upwards using (by fun_prop)

end ParametricIntegral
end
