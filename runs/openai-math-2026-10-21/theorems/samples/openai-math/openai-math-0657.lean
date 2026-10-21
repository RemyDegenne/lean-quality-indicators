namespace OAI

section

section

open Filter Set

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal

open Set MeasureTheory

open scoped RealInnerProductSpace

open Matrix

open scoped RealInnerProductSpace MatrixOrder

open Set Filter MeasureTheory

open MeasureTheory Filter Set Metric

open scoped Topology Pointwise NNReal

open Set MeasureTheory Measure Filter Module

open Set Filter MeasureTheory Measure Metric

open scoped Topology ContDiff

open Set Filter Metric

open scoped Topology NNReal

open Set MeasureTheory Filter

open scoped Topology ENNReal NNReal

open Set Filter MeasureTheory Measure ContinuousLinearMap

open scoped Topology Convolution NNReal

namespace CAT0Fillings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

lemma norm_fderiv_bump_convolution_le {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) (x : E) :
    ‖fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x‖ ≤ K := by
  rw [fderiv_bump_convolution μ hf, convolution_def]
  have hI := ((φ.contDiff_normed (μ := μ) (n := 1)).continuous.integrable_of_hasCompactSupport
    (μ := μ) φ.hasCompactSupport_normed).mul_const (K : ℝ)
  have H := norm_integral_le_of_norm_le hI (Eventually.of_forall (fun t => show
      ‖lsmul ℝ ℝ (φ.normed μ t) (fderiv ℝ f (x-t))‖ ≤ φ.normed μ t * K from by
    rw [lsmul_apply, norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t)]
    exact mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hf) (φ.nonneg_normed t)))
  simpa only [integral_mul_const, φ.integral_normed, one_mul] using H

end CAT0Fillings
end
end
end OAI
