@[expose] public section

open Set Filter TopologicalSpace Bornology

open scoped ENNReal NNReal Uniformity Topology

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

export Dist (dist)

variable [PseudoMetricSpace α]

attribute [instance_reducible, instance]
  PseudoMetricSpace.toUniformSpace PseudoMetricSpace.toBornology

export NNDist (nndist)

namespace Metric

variable {x y z : α} {δ ε ε₁ ε₂ : ℝ} {s : Set α}

theorem pos_of_mem_ball (hy : y ∈ ball x ε) : 0 < ε :=
  dist_nonneg.trans_lt hy

end Metric
end
