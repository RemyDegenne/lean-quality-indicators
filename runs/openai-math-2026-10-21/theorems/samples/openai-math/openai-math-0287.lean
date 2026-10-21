namespace OAI

section

open Set MeasureTheory Measure Filter Module

open Set Filter MeasureTheory Measure ContinuousLinearMap

open scoped Topology Convolution NNReal

open Set Filter MeasureTheory Measure Metric

open scoped Topology ContDiff

open Set Filter Metric

open Filter Set

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal

open Set MeasureTheory

open scoped RealInnerProductSpace

open Matrix

open scoped RealInnerProductSpace MatrixOrder

open Set Filter MeasureTheory

open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric

open scoped Topology Pointwise NNReal

open scoped ENNReal NNReal Topology

open Set MeasureTheory Filter

open scoped Topology NNReal

namespace SharpIntegralFillings

open Set MeasureTheory Filter

open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}

namespace IntegerChart

variable (C : IntegerChart X k)

omit [MeasurableSpace X] [BorelSpace X] in
lemma negate_action : C.negate.action = -C.action := by
  classical
  funext b π
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab,Pi.neg_apply]
    change (∫ z in C.domain,(-C.multiplicity z:ℤ)*C.scalar b z*C.jacobian π z) =
      -(∫ z in C.domain,(C.multiplicity z:ℝ)*C.scalar b z*C.jacobian π z)
    simp only [Int.cast_neg,neg_mul,integral_neg]
  · simp only [action,ite_eq_right hab,Pi.neg_apply,neg_zero]

end IntegerChart
end SharpIntegralFillings
end
end OAI
