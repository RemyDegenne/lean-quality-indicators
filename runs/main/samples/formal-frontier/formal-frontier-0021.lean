public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

@[simp]
theorem universalNormSubrepresentation_toSubmodule
    (A : Rep.{u} R G) (U : OpenNormalSubgroup G) :
    (universalNormSubrepresentation A U).toSubmodule =
      universalNormSubmodule A U :=
  rfl

end ContinuousGroupCohomology.LevelCompact
end
end
