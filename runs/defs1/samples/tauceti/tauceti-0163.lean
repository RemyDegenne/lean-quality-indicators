public section

namespace TauCeti

namespace FactorSet

universe u v

variable {G : Type u} {M : Type v} [Group G] [CommGroup M] [MulDistribMulAction G M]
  [TopologicalSpace G] [TopologicalSpace M]

namespace Extension

variable {α : FactorSet G M}

/-- **The twisted product is `M × G` as a topological space.** The multiplication is twisted by the
factor set, the topology is not. -/
def homeomorphProd (α : FactorSet G M) : α.Extension ≃ₜ M × G := (equivProd α).homeomorph

end Extension
end FactorSet
end TauCeti
end
