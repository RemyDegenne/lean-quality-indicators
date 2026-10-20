@[expose] public section

noncomputable section

open Filter Function Metric Set Topology

open scoped Finset ENNReal NNReal

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENNReal

variable {a b : ℝ≥0∞} {r : ℝ≥0} {x : ℝ≥0∞} {ε : ℝ≥0∞}

section TopologicalSpace

open TopologicalSpace

protected theorem Tendsto.div {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) (hmb : Tendsto mb f (𝓝 b))
    (hb : b ≠ ∞ ∨ a ≠ ∞) : Tendsto (fun a => ma a / mb a) f (𝓝 (a / b)) := by
  apply Tendsto.mul hma _ (tendsto_inv_iff.2 hmb) _ <;> simp [ha, hb]

end TopologicalSpace
end ENNReal
end
end
