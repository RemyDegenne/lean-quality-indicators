public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools DihedralGroup

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Setting46e

variable {S : Subgroup X} {w z : X} {V : Subgroup X} {i₀ j₀ : ℕ}

theorem card_D (hs : Setting46e t L 3 4 S w z V i₀ j₀) : Nat.card ↥(S ⊓ L) = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl := hs.standing.isSylowOf_inf hs.sylow
  rw [hSyl.card_eq]
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel hs.standing.config.lieModel
  have hbar : Nat.card (Bar L) = 3280 * 81 := by
    rw [Nat.card_congr e.toEquiv, SectionRank.OddCover.card_psl_two Nat.prime_three (by norm_num)
      hF]
    norm_num
  have hL : Nat.card ↥L = Nat.card (Bar L) * Nat.card ↥(pPrimeCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥L)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rw [hL, factorization_two_mul_odd (by rw [hbar]; norm_num) hodd, hbar,
    factorization_two_mul_odd (by norm_num) (by decide),
    show (3280 : ℕ) = 2 ^ 4 * 205 by norm_num,
    factorization_two_mul_odd (by norm_num) (by decide), Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same]
  norm_num

end Setting46e
end CFSG.ComponentClassification.HarrisLit
end
