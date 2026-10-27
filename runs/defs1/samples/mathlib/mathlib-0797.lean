public section

open Set Filter Bornology Topology

open scoped NNReal Uniformity

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

variable [PseudoMetricSpace α]

variable {γ : Type w} [MetricSpace γ]

namespace Metric

variable {x : γ} {s : Set γ}

/-- If a `PseudoMetricSpace` is a T₀ space, then it is a `MetricSpace`. -/
abbrev _root_.MetricSpace.ofT0PseudoMetricSpace (α : Type*) [PseudoMetricSpace α] [T0Space α] :
    MetricSpace α where
  toPseudoMetricSpace := ‹_›
  eq_of_dist_eq_zero hdist := (Metric.inseparable_iff.2 hdist).eq

end Metric
end
