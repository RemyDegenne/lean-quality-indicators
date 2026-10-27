public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_bar {X K R : Subgroup G} (hKX : K ≤ X) (hR : IsSylowOf 2 R K) :
    IsSylowOf 2 (bar X R) (bar X K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff_card] at hR ⊢
  refine ⟨bar_mono hR.1, ?_⟩
  rw [card_bar_of_pGroup (hR.1.trans hKX) (IsPGroup.of_card hR.2), hR.2,
    factorization_card_bar hKX]

end CFSG.ComponentClassification.Asc76X
end
