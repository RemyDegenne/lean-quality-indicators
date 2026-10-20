public section

open scoped InnerProductSpace

namespace ContRepresentation

variable {R G V : Type*} [Ring R] [Group G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V]

section Monoid

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

theorem isUnitary_iff_norm_map (π : ContRepresentation 𝕜 G V) :
    IsUnitary π ↔ ∀ g v, ‖π g v‖ = ‖v‖ := by
  constructor
  · intro hπ g
    exact (LinearMap.norm_map_iff_inner_map_map (π g)).mpr (hπ g)
  · intro hπ g
    exact (LinearMap.norm_map_iff_inner_map_map (π g)).mp (hπ g)

end Monoid
end ContRepresentation
end
