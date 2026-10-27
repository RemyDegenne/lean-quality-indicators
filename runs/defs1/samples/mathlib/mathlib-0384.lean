@[expose] public section

open Function Topology

namespace ContinuousMap

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

variable {f g : C(α, β)}

variable (α)

/-- The identity as a continuous map. -/
protected def id : C(α, α) where
  toFun := id

end ContinuousMap
end
