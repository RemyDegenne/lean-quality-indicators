public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem subgroup_card_lt_of_lt {G : Type u} [Group G] [Finite G]
    (first second : Subgroup G) (hstrict : first < second) : Nat.card first < Nat.card second := by
  classical
  let : Fintype first := Fintype.ofFinite _
  let : Fintype second := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_not_surjective (Subgroup.inclusion hstrict.le)
    (Subgroup.inclusion_injective hstrict.le)
  intro hsurjective
  apply hstrict.not_ge
  intro element helement
  obtain ⟨preimage, hpreimage⟩ := hsurjective ⟨element, helement⟩
  have heq : (preimage : G) = element := congrArg Subtype.val hpreimage
  exact heq ▸ preimage.property

end CFSG.RankThreeEvenClassification.Helpers
end
