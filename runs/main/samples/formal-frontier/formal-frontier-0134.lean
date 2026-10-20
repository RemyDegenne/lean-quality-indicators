public section

set_option warningAsError true

open CategoryTheory Topology

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]

variable [IsTopologicalGroup G] [CompactSpace G]

variable (A : Rep.{u} R G) (L : LevelCompact A)

lemma finiteTateNegative_eq_positiveHomology (S : OpenNormalSubgroup G) (n : ℕ) :
    finiteTateNegative A L S n =
      @CompHausAddCommGrp.FiniteBar.positiveHomology
        R (G ⧸ S.toSubgroup) _ _ (Fintype.ofFinite _)
        (A.quotientToInvariants S.toSubgroup)
        (L.topology S.toOpenSubgroup) (L.compact S.toOpenSubgroup)
        (L.t2 S.toOpenSubgroup) (L.topologicalAddGroup S.toOpenSubgroup)
        (continuous_quotientToInvariants_action A L S) n := rfl

end ContinuousGroupCohomology.LevelCompact
end
