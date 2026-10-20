public section

open MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace G] (B : F →L[ℝ] E →L[ℝ] G)

lemma condExp_mul_of_stronglyMeasurable_right {f g : Ω → ℝ} (hg : StronglyMeasurable[m] g)
    (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * g | m] =ᵐ[μ] μ[f | m] * g :=
  condExp_bilin_of_aestronglyMeasurable_right (.mul ℝ ℝ)
    hg.aestronglyMeasurable hfg hf

end MeasureTheory
end
