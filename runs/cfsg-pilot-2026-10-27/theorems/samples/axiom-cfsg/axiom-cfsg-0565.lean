public section

namespace CFSG.ComponentClassification.AS81

open Subgroup Q47 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

open CFSG.ComponentClassification.AS81.HeSylow

variable {G : Type} [Group G]

namespace VCode

variable {Q : Subgroup G} {z : G} (c : VCode Q z)

variable {c}

theorem pow_mod_two (hs : Std Q z) (m : ℕ) : z ^ (m % 2) = z ^ m := by
  rw [← orderOf_z hs]
  exact pow_mod_orderOf z m

end VCode
end CFSG.ComponentClassification.AS81
end
