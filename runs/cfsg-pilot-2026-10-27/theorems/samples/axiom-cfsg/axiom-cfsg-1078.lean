public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G]

section Basic

variable {x : G} {S₀ R₀ : Subgroup (CentralizerBar x)} {T : Subgroup G}

theorem Rg_le : Rg x R₀ T ≤ T := inf_le_left

end Basic
end CFSG.GH74.Generic.S45
end
