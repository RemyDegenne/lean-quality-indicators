public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

open scoped commutatorElement

namespace Wales1411W

variable {G : Type} [Group G] [Finite G]

section Frame

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem card_img148_A (hA3 : IsPGroup 3 A) : Nat.card (img148 A Y A) = Nat.card A := by
  have hinj : Function.Injective ((QuotientGroup.mk' (ker148 A Y)).comp
      (Subgroup.inclusion (le_sup_right : A ≤ Y ⊔ A))) := by
    intro x y hxy
    exact Subtype.ext (eq_of_mk_eq_of_mem_A hA3 x.2 y.2 hxy)
  have h1 : img148 A Y A = ((QuotientGroup.mk' (ker148 A Y)).comp
      (Subgroup.inclusion (le_sup_right : A ≤ Y ⊔ A))).range := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Subgroup.inclusion le_sup_right a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  rw [h1, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]

end Frame
end Wales1411W
end CFSG.RankThree.PartTwo.Sec14
end
