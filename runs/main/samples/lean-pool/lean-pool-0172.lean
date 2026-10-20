@[expose] public section

noncomputable section

namespace EulerSobolevDerivativeNorm

open MeasureTheory FourierTransform EulerSobolev EulerSobolevProducts

open scoped SchwartzMap ENNReal ContDiff LineDeriv

theorem pointwise_le_L2_third_derivatives (f : 𝓢(Domain 4, ℂ)) (x : Domain 4) :
    ‖f x‖ ≤ embeddingConstant 4 3 (by norm_num) * 25 *
      (‖(f.toLp 2 :)‖ + (2 * Real.pi) ^ (-3 : ℤ) *
        ∑ i : Fin 4, ‖((directional 4 3 (EuclideanSpace.single i 1) f).toLp 2 :)‖) := by
  have hA := norm_apply_le_sobolevNorm 4 3 (by norm_num) f x
  have hB := mul_le_mul_of_nonneg_left (sobolevNorm_three_le_pure_derivatives 4 f)
    (show 0 ≤ embeddingConstant 4 3 (by norm_num) from norm_nonneg _)
  refine hA.trans (hB.trans_eq ?_)
  norm_num
  ring

end EulerSobolevDerivativeNorm
end
end
