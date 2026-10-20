@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function TopologicalSpace

open scoped Topology Filter ENNReal Interval NNReal

variable {ι 𝕜 ε ε' E F A : Type*} [NormedAddCommGroup E]
  [TopologicalSpace ε] [ENormedAddMonoid ε] [TopologicalSpace ε'] [ENormedAddMonoid ε']

namespace IntervalIntegrable

variable [NormedRing A] {f g : ℝ → ε} {a b : ℝ} {μ : Measure ℝ}

variable [PseudoMetrizableSpace ε]

theorem comp_add_right_iff {c : ℝ} (h : ‖f (min a b + c)‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (x + c)) volume a b
      ↔ IntervalIntegrable f volume (a + c) (b + c) where
  mp hf := by simpa using hf.comp_add_right (-c)
  mpr hf := by
    have : ‖f (min (a + c) (b + c))‖ₑ ≠ ⊤ := by rwa [min_add_add_right]
    simpa using hf.comp_add_right c

end IntervalIntegrable
end
end
