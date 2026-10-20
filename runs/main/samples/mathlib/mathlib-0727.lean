@[expose] public section

open Set Filter Function Topology

noncomputable section

namespace TopologicalSpace

universe u

variable {α : Type u} {β : Type*} [t : TopologicalSpace α] {B : Set (Set α)} {s : Set α}

variable (α)

variable {α}

theorem IsSeparable.of_subtype (s : Set α) [SeparableSpace s] : IsSeparable s := by
  simpa using isSeparable_range (continuous_subtype_val (p := (· ∈ s)))

end TopologicalSpace
end
end
