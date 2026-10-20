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

@[simp]
lemma finiteTateZeroπ_apply (S : OpenNormalSubgroup G)
    (x : group A L (⊤ : OpenSubgroup G)) :
    finiteTateZeroπ A L S x = QuotientAddGroup.mk x :=
  rfl

end ContinuousGroupCohomology.LevelCompact
end
end
