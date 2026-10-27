public section

namespace CFSG.Quasithin.F53Push

open CFSG.Quasithin.F53Mod Equiv

theorem card_le_four {B : Subgroup (Perm (Fin 5))} (hB : B ≤ S5Syl) (hsq : ∀ b ∈ B, b * b = 1) :
    Nat.card B ≤ 4 := by
  by_contra hlt
  push Not at hlt
  have hdvd : Nat.card B ∣ 8 := card_S5Syl ▸ Subgroup.card_dvd_of_le hB
  have hmem : Nat.card B ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have h8 : Nat.card B = 8 := by
    have : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [this] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hBS : B = S5Syl := Subgroup.eq_of_le_of_card_ge hB (by rw [card_S5Syl, h8])
  have hg : S5g ∈ B := by
    rw [hBS]
    exact Subgroup.subset_closure (Or.inl rfl)
  exact (show S5g * S5g ≠ 1 by decide +kernel) (hsq _ hg)

end CFSG.Quasithin.F53Push
end
