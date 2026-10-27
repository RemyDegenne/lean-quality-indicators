public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

theorem oddCore_quotient_eq_bot {A : Type*} [Group A] [Finite A] :
    CFSG.oddCore (A ⧸ CFSG.oddCore A) = ⊥ := by
  obtain ⟨e⟩ := oddQuot_equiv_of_surj (QuotientGroup.mk' (CFSG.oddCore A))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact odd_card_oddCore' A)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore (A ⧸ CFSG.oddCore A))
  have h2 : Nat.card ((A ⧸ CFSG.oddCore A) ⧸ CFSG.oddCore (A ⧸ CFSG.oddCore A)) =
      Nat.card (A ⧸ CFSG.oddCore A) := (Nat.card_congr e.toEquiv).symm
  have hpos : 0 < Nat.card (A ⧸ CFSG.oddCore A) := Nat.card_pos
  have h3 : Nat.card ↥(CFSG.oddCore (A ⧸ CFSG.oddCore A)) = 1 := by
    rw [h2] at h1
    nlinarith
  exact Subgroup.card_eq_one.1 h3

end CFSG.EvenSporadicStandard.Induction.Hyp
end
