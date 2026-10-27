public section

namespace CFSG.GH74.Uniqueness.SU.SU9

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.Uniqueness.SU.SU7
  CFSG.GH74.GLS.Bg.TwoGroups CFSG

namespace Cfg

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem card_A (hc : Ctx19 S U M V x z A B R) : Nat.card A = 16 := hc.c19.isE16_A.2

end Cfg
end CFSG.GH74.Uniqueness.SU.SU9
end
