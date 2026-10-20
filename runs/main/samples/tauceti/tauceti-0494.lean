public section

open Filter InnerProductSpace Metric Set Topology

open scoped Gradient NNReal

noncomputable section

namespace ContDiffAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {x : E}

open TauCeti

theorem hasFDerivAt_negativeGradientRemainder (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (negativeGradientRemainder f x) (0 : E →L[ℝ] E) x := by
  have hlinear : HasFDerivAt (fun y ↦ hessianOperator f x (y - x)) (hessianOperator f x) x := by
    simpa only [map_sub] using
      (hessianOperator f x).hasFDerivAt.sub_const (hessianOperator f x x)
  have hfun : negativeGradientRemainder f x =
      fun y ↦ (-∇ f) y + hessianOperator f x (y - x) :=
    funext fun y ↦ negativeGradientRemainder_apply f x y
  rw [hfun]
  convert hf.hasFDerivAt_neg_gradient.add hlinear using 1
  simp

end ContDiffAt
end
end
