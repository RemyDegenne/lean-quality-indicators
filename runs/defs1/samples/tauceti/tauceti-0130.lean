public section

namespace TauCeti

variable (Γ : Type*) [Group Γ] [LinearOrder Γ]

/-- A **convex subgroup** of a group `Γ` with a linear order is a subgroup
that is order-convex: if `a ≤ x ≤ b` and `a, b ∈ H`, then `x ∈ H`. -/
structure ConvexSubgroup extends Subgroup Γ where
  ordConnected' : carrier.OrdConnected

end TauCeti
end
