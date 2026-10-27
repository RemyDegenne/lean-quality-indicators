public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

open CFSG.LieType.Steinberg.Sp (blockMat)

open CFSG.QuasithinUnique.Lin2.Five (tauEquiv tauMat)

open scoped MatrixGroups Matrix

theorem sylow_conj_sp8 (hcard : Nat.card Sp8 = 3 ^ 4 * 13045760) (S : Subgroup Sp8)
    (hS : Nat.card S = 3 ^ 4) : ∃ m : Sp8, ∀ x, x ∈ spT0 ↔ m⁻¹ * x * m ∈ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM : 3 ^ 4 ∣ Nat.card (⊤ : Subgroup Sp8) := by
    rw [Subgroup.card_top, hcard]
    exact Dvd.intro _ rfl
  have hM' : ¬ 3 ^ (4 + 1) ∣ Nat.card (⊤ : Subgroup Sp8) := by
    rw [Subgroup.card_top, hcard]
    intro h
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (by norm_num : (3 ^ 4 * 13045760 : ℕ) ≠ 0)).1 h
    have hfac : (3 ^ 4 * 13045760 : ℕ).factorization 3 = 4 := by
      rw [Nat.factorization_mul (by norm_num) (by norm_num)]
      simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three]
      have h2 : (13045760 : ℕ).factorization 3 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)
      simp [h2]
    omega
  obtain ⟨m, -, hm⟩ := exists_conj_of_sylow_in (p := 3) (⊤ : Subgroup Sp8) hM hM'
    S spT0 le_top le_top hS (by rw [card_spT0]; norm_num)
  exact ⟨m, hm⟩

end CFSG.AGLEmbedding.KFactProofs.Sp48
end
