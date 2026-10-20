@[expose] public section

noncomputable section

open Filter Function Metric Set Topology

open scoped Finset ENNReal NNReal

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENNReal

variable {a b : ℝ≥0∞} {r : ℝ≥0} {x : ℝ≥0∞} {ε : ℝ≥0∞}

section TopologicalSpace

open TopologicalSpace

protected theorem continuousAt_const_mul {a b : ℝ≥0∞} (h : a ≠ ∞ ∨ b ≠ 0) :
    ContinuousAt (a * ·) b :=
  Tendsto.const_mul tendsto_id h.symm

end TopologicalSpace
end ENNReal
end
end
