namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped NNReal ENNReal

open Set Filter

open scoped Topology

open MeasureTheory ProbabilityTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

open MeasureTheory Filter Set

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal Topology

open scoped NNReal ENNReal Topology

open scoped NNReal Topology

open Set

open Set Filter MeasureTheory

open scoped BigOperators

open scoped Topology NNReal

open scoped Topology BigOperators

open scoped ENNReal NNReal

open MeasureTheory Set

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal BigOperators Classical

open Classical

open scoped ENNReal NNReal Topology BigOperators MatrixOrder

open scoped NNReal BigOperators

open MeasureTheory Filter Set

open scoped Topology BigOperators

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal BigOperators Classical

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal BigOperators Classical

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal BigOperators Classical

open MeasureTheory ProbabilityTheory Filter Set

open scoped Topology BigOperators

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal BigOperators Classical

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal BigOperators Classical

open MeasureTheory ProbabilityTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma coordinateLaw_mgf {ε : ℝ} (he : ε ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    mgf id (coordinateLaw ε) t =
      (Real.exp ((1-ε)*t^2/2) + Real.exp ((1+ε)*t^2/2))/2 := by
  have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := Real.toNNReal (1-ε)) t
  have h2 := integrable_exp_mul_gaussianReal (μ := 0) (v := Real.toNNReal (1+ε)) t
  unfold coordinateLaw mgf
  simp only [id_eq]
  rw [integral_add_measure (h1.smul_measure (by norm_num))
    (h2.smul_measure (by norm_num)), integral_smul_measure, integral_smul_measure]
  change (1/2 : ℝ≥0∞).toReal * mgf id (gaussianReal 0 (Real.toNNReal (1-ε))) t +
    (1/2 : ℝ≥0∞).toReal * mgf id (gaussianReal 0 (Real.toNNReal (1+ε))) t = _
  simp only [mgf_id_gaussianReal, zero_mul, zero_add,
    Real.coe_toNNReal _ (by linarith [he.2] : 0 ≤ 1-ε),
    Real.coe_toNNReal _ (by linarith [he.1] : 0 ≤ 1+ε)]
  norm_num
  ring

end MicroscopicJamming
end
end OAI
