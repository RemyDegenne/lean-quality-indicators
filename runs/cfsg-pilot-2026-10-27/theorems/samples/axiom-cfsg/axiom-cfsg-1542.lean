public section

namespace CFSG.RankThree.SubgroupLists

open scoped commutatorElement

variable {G : Type*} [Group G] {Z : Subgroup G}

variable [Z.Normal]

theorem map_commutator_comap (L : Subgroup (G ⧸ Z)) [Group.IsPerfect L] :
    (⁅L.comap (QuotientGroup.mk' Z), L.comap (QuotientGroup.mk' Z)⁆).map (QuotientGroup.mk' Z) =
      L := by
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective Z), Subgroup.commutator_eq_self]

end CFSG.RankThree.SubgroupLists
end
