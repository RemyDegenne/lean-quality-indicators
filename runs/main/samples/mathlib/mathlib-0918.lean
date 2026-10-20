@[expose] public section

universe u

open Filter Function Order Set

open Topology

variable {ι α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

namespace Opens

@[simp]
theorem mem_sup {s t : Opens α} {x : α} : x ∈ (s ⊔ t) ↔ x ∈ s ∨ x ∈ t :=
  .rfl

end Opens
end TopologicalSpace
end
