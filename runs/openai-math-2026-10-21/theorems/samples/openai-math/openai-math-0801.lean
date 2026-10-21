namespace OAI

section

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal Topology

open scoped Topology

open Set

open MeasureTheory Filter

open scoped NNReal Topology

open MeasureTheory Filter Set Metric Function ODE

open MeasureTheory ProbabilityTheory Filter Set

namespace ExactSLEGreen

lemma green_generator_zero (a : ℝ) (ha : a ≠ 0) (v : State) (hv : 0 < Y v) :
    (1/2 : ℝ) * fderiv ℝ (fun w => fderiv ℝ (physicalGreen a) w noise) v noise +
      fderiv ℝ (physicalGreen a) v (physicalDrift a v) = 0 := by
  rw [green_second_noise a v hv,(hasFDerivAt_physicalGreen a v hv).fderiv]
  simp only [smul_apply,smul_eq_mul,logGreenDeriv_drift a v hv]
  have hq := (Q_pos hv).ne'
  unfold alpha p
  field_simp
  unfold Q
  ring

end ExactSLEGreen
end
end OAI
