public section

open InnerProductSpace Set

open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {K : ℝ≥0}

theorem hasDerivAt_fderiv_negativeGradientFlow (f : E → ℝ) (hf : LipschitzWith K (∇ f))
    (hfs : ContDiff ℝ 2 f) (x : E) (t : ℝ) :
    HasDerivAt (fun τ ↦ fderiv ℝ (negativeGradientFlow f hf τ) x)
      (-(fderiv ℝ (∇ f) (negativeGradientFlow f hf t x)).comp
        (fderiv ℝ (negativeGradientFlow f hf t) x)) t := by
  have h := hasDerivAt_fderiv_flowOfLipschitz hf.neg
    (hfs.gradient_right (m := 1) (by norm_num)).neg x t
  rw [fderiv_neg, ContinuousLinearMap.neg_comp] at h
  exact h

end TauCeti
end
