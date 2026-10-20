@[expose] public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

open CategoryTheory Topology

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]

variable [IsTopologicalGroup G] [CompactSpace G]

variable (A : Rep.{u} R G) (L : LevelCompact A)

lemma finiteTateNegativeDeflation_refl
    (S : OpenNormalSubgroup G)
    [Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] (n : ℕ) :
    finiteTateNegativeDeflation A L S S le_rfl n = 𝟙 _ := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ :=
    (groupHomologyAddEquivFiniteTateNegative A L S n).surjective x
  change
    finiteTateNegativeDeflation A L S S le_rfl n
        (groupHomologyAddEquivFiniteTateNegative A L S n y) =
      groupHomologyAddEquivFiniteTateNegative A L S n y
  rw [← groupHomologyAddEquivFiniteTateNegative_finiteNegativeDeflation
    A L S S le_rfl n y]
  simpa using congrArg (groupHomologyAddEquivFiniteTateNegative A L S n)
    (CategoryTheory.congr_fun
      (finiteNegativeDeflation_refl A S.toSubgroup (n + 1)) y)

end ContinuousGroupCohomology.LevelCompact
end
end
