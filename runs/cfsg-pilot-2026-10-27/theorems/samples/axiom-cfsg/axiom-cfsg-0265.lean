public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.SmallOddCore

variable {G : Type} [Group G]

theorem fi24OutR_isCoatom_map {J' R' : Subgroup G} (h : J' ≤ R') {M' : Subgroup J'}
    (hM : IsCoatom M') :
    IsCoatom ((M'.map (Subgroup.inclusion h)).subgroupOf (J'.subgroupOf R')) := by
  have e : (M'.map (Subgroup.inclusion h)).subgroupOf (J'.subgroupOf R') =
      M'.map (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom := by
    ext p
    rw [mem_subgroupOf]
    constructor
    · rintro ⟨g, hg, hgp⟩
      exact ⟨g, hg, Subtype.ext hgp⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩
  rw [e]
  exact (OrderIso.isCoatom_iff (Subgroup.subgroupOfEquivOfLe h).symm.mapSubgroup M').2 hM

end CFSG.EvenSporadicStandard.Induction
end
