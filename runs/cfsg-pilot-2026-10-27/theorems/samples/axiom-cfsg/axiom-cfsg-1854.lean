public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Setting

variable {G : Type*} [Group G] (S : Setting G)

variable [Finite G]

theorem card_range_eq_half : Nat.card S.conjHom.range * 2 = Nat.card S.M := by
  have h := S.card_conjHom_range
  rwa [S.card_center_Q] at h

end Setting
end CFSG.LargeExtraspecial
end
