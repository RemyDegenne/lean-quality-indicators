@[expose] public section

universe u v w

namespace QuotientGroup

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The canonical continuous homomorphism to the identity-component quotient. -/
def connectedComponentQuotientMk : G →ₜ* connectedComponentQuotient G where
  toMonoidHom := mk' (Subgroup.connectedComponentOfOne G)
  continuous_toFun := continuous_mk

end QuotientGroup
end
