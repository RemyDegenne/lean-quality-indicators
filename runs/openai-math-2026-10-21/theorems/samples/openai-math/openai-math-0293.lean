namespace OAI

open MeasureTheory Set

open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

namespace StandardMapEntropy

lemma middleBridgeConstant_ne_top : middleBridgeConstant ≠ ∞ := by
  exact ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num) bridgeLocalConstant_ne_top) bridgeAreaScale_pos.ne'

end StandardMapEntropy
end OAI
