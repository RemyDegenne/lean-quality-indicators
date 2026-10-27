public section

namespace CFSG.OddTranspositions.PartThree.EightOne

open CFSG.Timmesfeld.Bridge.Asc72

theorem odd_card_oddCore {X : Type} [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : CFSG.oddCore X = CFSG.pPrimeCore 2 X :=
    (CFSG.oddCore_eq_piCore X).trans (CFSG.pPrimeCore_eq_piCore X 2).symm
  rw [h]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

end CFSG.OddTranspositions.PartThree.EightOne
end
