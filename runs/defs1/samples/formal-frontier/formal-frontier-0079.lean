public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompact

universe uR uG uA

variable {R : Type uR} [CommRing R]

variable {G : Type uG} [Group G] [TopologicalSpace G]

variable [IsTopologicalGroup G] [CompactSpace G]

variable (A : Rep.{uA} R G) (L : LevelCompact A)

section AlgebraicComparison

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]

variable [IsTopologicalGroup G] [CompactSpace G]

variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- The compact group at an open level has the corresponding invariant submodule
as its underlying additive group. -/
def openSubgroupInvariantsAddEquivGroup (U : OpenSubgroup G) :
    openSubgroupInvariants A U ≃+ group A L U := by
  change openSubgroupInvariants A U ≃+ openSubgroupInvariants A U
  exact AddEquiv.refl _

end AlgebraicComparison
end ContinuousGroupCohomology.LevelCompact
end
end
