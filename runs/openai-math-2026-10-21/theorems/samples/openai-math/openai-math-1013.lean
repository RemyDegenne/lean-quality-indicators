namespace OAI

noncomputable section

open MeasureTheory

namespace CubicFirstMoment

lemma cubicThetaRadialWeakSolution_bound (A : ℝ) (F : CubicThetaRadialL2) :
    ‖cubicThetaRadialWeakSolution A F‖ ≤ ‖F‖ := by
  unfold cubicThetaRadialWeakSolution
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖innerSL ℂ F‖*‖cubicThetaRadialInclusion A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖F‖*1 := by
      rw [innerSL_apply_norm]
      exact mul_le_mul_of_nonneg_left (cubicThetaRadialInclusion_norm A) (_root_.norm_nonneg _)
    _ = _ := mul_one _

end CubicFirstMoment
end
end OAI
