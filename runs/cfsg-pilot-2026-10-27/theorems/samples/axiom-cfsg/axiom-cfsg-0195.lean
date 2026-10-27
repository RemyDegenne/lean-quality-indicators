public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.P22k2

open CFSG.Open Subgroup CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

section KleinFour

open scoped IsKleinFour

variable (W : Type*) [Group W] [IsKleinFour W]

theorem s3_card_omega : Nat.card {v : W // v ≠ 1} = 3 := by
  classical
  have h4 : Nat.card W = 4 := IsKleinFour.card_four
  haveI : Fintype W := Fintype.ofFinite W
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [Nat.card_eq_fintype_card] at h4
  omega

end KleinFour
end CFSG.LocalAnalysis.UniquenessCase.UC22.P22k2
end
