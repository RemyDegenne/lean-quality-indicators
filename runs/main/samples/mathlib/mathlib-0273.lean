@[expose] public section

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

namespace ProbabilityTheory

variable {α : Type*}

section IsMeasurableRatCDF

variable {f : α → ℚ → ℝ}

variable [MeasurableSpace α]

lemma IsMeasurableRatCDF.tendsto_atTop_one {f : α → ℚ → ℝ} (hf : IsMeasurableRatCDF f) (a : α) :
    Tendsto (f a) atTop (𝓝 1) := (hf.isRatStieltjesPoint a).tendsto_atTop_one

end IsMeasurableRatCDF
end ProbabilityTheory
end
