public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}
  {h k k' : G}

theorem Lbar_sup_le_Mbar (S : Setting G) (k k' : G) : S.Lbar k ⊔ S.Lbar k' ≤ S.Mbar :=
  sup_le (S.Lbar_le_Mbar k) (S.Lbar_le_Mbar k')

end CFSG.LargeExtraspecial.S11
end
