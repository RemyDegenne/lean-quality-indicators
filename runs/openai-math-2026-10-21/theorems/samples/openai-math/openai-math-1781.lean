namespace OAI

universe u181

noncomputable section

namespace SharpLiebThirring.OperatorProof

open MeasureTheory Set Filter

open scoped Topology

lemma L2_norm_sq_eq_integral (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 := by
  rw [@norm_sq_eq_re_inner ℂ,L2.inner_def]
  change Complex.reCLM (∫ x, inner ℂ (f x) (f x)) = _
  rw [← Complex.reCLM.integral_comp_comm (L2.integrable_inner f f)]
  congr 1
  ext x
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (f x)).symm

end SharpLiebThirring.OperatorProof
end
end OAI
