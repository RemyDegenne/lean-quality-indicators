public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open scoped commutatorElement

theorem map_pPrimeCore_le_pPrimeCore {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f) :
    (pPrimeCore 2 X).map f ≤ pPrimeCore 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_sSup
  refine ⟨Subgroup.Normal.map inferInstance f hf, ?_⟩
  have h1 : Nat.card ((pPrimeCore 2 X).map f) ∣ Nat.card (pPrimeCore 2 X) :=
    card_map_dvd _ _
  exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card

end CFSG.ComponentClassification.GrSLit
end
