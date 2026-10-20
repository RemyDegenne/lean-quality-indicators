@[expose] public section

open Function Topology

namespace ContinuousMap

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

variable {f g : C(α, β)}

variable (α)

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

end ContinuousMap
end
