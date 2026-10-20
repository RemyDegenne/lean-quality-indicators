public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

section Definitions

variable {G : Type*} [TopologicalSpace G] [Group G]

/-- **A torus** of a topological group: a compact, connected, commutative subgroup. -/
structure IsTorus (T : Subgroup G) : Prop where
  isCompact : IsCompact (T : Set G)
  isConnected : IsConnected (T : Set G)
  isMulCommutative : IsMulCommutative T

end Definitions
end TauCeti.Lie
end
end
