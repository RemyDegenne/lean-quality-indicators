namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry

open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section

universe u v

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

namespace MemoryPrecision

open NoiselessRegression

section WeightedImage

variable {X : Type*} [MeasurableSpace X] {d m N : ℕ}

lemma weighted_image_finite (μ : Measure X) [IsFiniteMeasure μ] (ι : X → Space d)
    (h : X → ℝ≥0∞) (hh1 : ∀ x, h x ≤ 1) :
    IsFiniteMeasure ((μ.withDensity h).map ι) := by
  let := isFiniteMeasure_withDensity (μ := μ) (ne_of_lt ((lintegral_mono hh1).trans_lt (by simp)))
  infer_instance

end WeightedImage
end MemoryPrecision
end
end OAI
