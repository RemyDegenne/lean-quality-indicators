public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open

open CFSG.LargeEvenClassification.Helpers (pGeneratorRank pGeneratorRank_le_generators)

open CFSG.LocalAnalysis.ComponentInitial (isCharacteristicP_of_mulEquiv
  not_isComponent_of_isCharacteristicP_two centralizer_singleton_eq_normalizer_zpowers)

variable {G : Type*} [Group G]

theorem involution_centralizer_core_and_components [Finite G]
    (hchar : CFSG.IsCharacteristicPType G 2) {x : G} (hx : orderOf x = 2) :
    CFSG.IsCharacteristicP 2 (centralizer ({x} : Set G)) ∧
      CFSG.pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ ∧
      ∀ K : Subgroup (centralizer ({x} : Set G)), ¬ CFSG.IsComponent K := by
  have := Fact.mk Nat.prime_two
  have hloc : CFSG.IsPLocal 2 (centralizer ({x} : Set G)) := by
    refine ⟨zpowers x, ?_, ?_, centralizer_singleton_eq_normalizer_zpowers hx⟩
    · intro h
      rw [zpowers_eq_bot] at h
      rw [h, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hx, pow_one]
  have hC := hchar _ hloc
  exact ⟨hC, CFSG.pPrimeCore_eq_bot_of_isCharacteristicP _ 2 hC,
    not_isComponent_of_isCharacteristicP_two hC⟩

end CFSG.LocalAnalysis.GorensteinLyons
end
