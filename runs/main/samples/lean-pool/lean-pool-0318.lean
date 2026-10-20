@[expose] public section

namespace Domain.Neighborhood.Exercise422

open Domain.Neighborhood Domain.Neighborhood.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)

theorem succ_mem_nats {n : M} (hn : n ∈ nats zero succ) : succ n ∈ nats zero succ := by
  intro x hx
  exact hx (Or.inr ⟨n, hn x hx, rfl⟩)

end Domain.Neighborhood.Exercise422
end
