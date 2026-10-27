@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]

theorem odd_Opp_of_no_two {G : Type} [Group G] [Finite G] {A : Subgroup G} (hA : IsPGroup 3 A)
    (hno : ∀ R : Subgroup G, IsPGroup 2 R → A ≤ Nor R → R = ⊥) :
    Odd (Nat.card (Opp 3 (⊤ : Subgroup G))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup G := Opp 3 (⊤ : Subgroup G) with hO
  by_contra hodd
  have h2dvd : 2 ∣ Nat.card O := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have hOcop : Nat.Coprime 3 (Nat.card O) := L14.Opp_coprime 3 (⊤ : Subgroup G)
  have h3dvd : ¬ 3 ∣ Nat.card O := fun hd =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hOcop hd
  have hOn : O.Normal := ⟨fun x hx g => by
    simpa using L14.Opp_conj_mem (p := 3) (H := (⊤ : Subgroup G)) (Subgroup.mem_top g) hx⟩
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := by
    haveI := hOn
    exact Subgroup.le_normalizer_of_normal
  obtain ⟨R, hRsyl, -, hAR⟩ := CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime
    (q := 3) (r := 2) (A := A) (K := O) (P := ⊥) Nat.prime_three Nat.prime_two hA hAO h3dvd
    bot_le IsPGroup.of_bot Subgroup.le_normalizer_of_normal
  have hR2 : IsPGroup 2 R := CFSG.ABGLocalTools.IsSylowOf.isPGroup hRsyl
  have hRbot : R = ⊥ := hno R hR2 hAR
  have hndvd : ¬ 2 ∣ R.relIndex O := (CFSG.ABGLocalTools.isSylowOf_iff.mp hRsyl).2.2
  exact hndvd (by rw [hRbot, Subgroup.relIndex_bot_left]; exact h2dvd)

end CFSG.RankThree.PartTwo.Sec21.FF81
end
