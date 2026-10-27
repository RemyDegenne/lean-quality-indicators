public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

open scoped commutatorElement IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.facts14610_rank4_of_sylow {H : Subgroup G} {u : G} {I I₂ K : Subgroup G}
    (c : Facts14610 T M H u I I₂) (hK : Concl14610List T M I I₂ K) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hA : IsAlt 6 (OTwoQuot K) ∨ IsAlt 7 (OTwoQuot K)) (hW : Nat.card (wOf1469 K) = 2 ^ 4) :
    Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3 :=
  le_antisymm (ModB.rank4U_of_sylow c hK hsyl hA hW)
    (Setting146.eight_le_card_conjClosure_I₂ c.toHyp14610)

end CFSG.Quasithin
end
