public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

variable {G : Type} [Group G] [Finite G]

open scoped commutatorElement IsMulCommutative

open CFSG.ABGLocalTools

theorem exists_order_five_of_isAlt {L' : Subgroup G} (hL : IsAlt (Bar2 L') 5) :
    ∃ b : ↥L', orderOf b = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact exists_prime_orderOf_dvd_card' 5 (five_dvd_card_of_isAlt hL)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
end
