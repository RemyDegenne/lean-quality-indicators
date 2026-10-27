public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.RecipeExcLang CFSG.StandardType.TwE6RootKill

theorem exists_twLangData_fixSubfield (h5 : SubfieldLangDatumFive) (h3 : SubfieldLangDatumThree)
    (h34 : SubfieldLangDatumThreeFour) {K₀ K : Type} [Field K₀] [Finite K₀] [Field K] [Finite K]
    (ι : K₀ →+* K) {σ₀ : K₀ ≃+* K₀} (σ : K ≃+* K) {m p : ℕ} (hm : 1 ≤ m)
    (hK₀ : Nat.card K₀ = (2 ^ m) ^ 2) (hK : Nat.card K = (2 ^ (m * p)) ^ 2)
    (hσ₀ : ∀ c, σ₀ c = c ^ 2 ^ m) (hσ : ∀ c, σ c = c ^ 2 ^ (m * p)) (hp : p.Prime)
    (hpq : p ∣ 2 ^ m + 1) {A₀ : Subgroup (ModGL TwistTag.E6.tag K₀)}
    (hAI : A₀ ≤ twistedE6InndiagGL K₀ σ₀) (hA : IsElemAbelian p A₀)
    (hr : p ^ (if p = 3 then 4 else 5) ≤ Nat.card A₀)
    (hU : TwNormTwo K σ (A₀.map (baseChangeGL ι))) :
    ∃ D₀ : TwLangData K₀ σ₀ (2 ^ m) A₀, D₀.c = 1 := by
  haveI : CharP K₀ 2 := charP_two_of_card_sq hK₀
  have h2 : ringChar K₀ = 2 := ringChar.eq K₀ 2
  by_cases hp3 : p = 3
  · subst hp3
    rw [if_pos rfl] at hr
    by_cases h35 : 3 ^ 5 ≤ Nat.card A₀
    · exact h3 K₀ σ₀ (2 ^ m) hK₀ hσ₀ h2 hpq A₀ hAI hA h35
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Finite A₀ := Nat.finite_of_card_ne_zero (lt_of_lt_of_le (by norm_num) hr).ne'
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (TableB.isPGroup_of_isElemAbelian hA)
    rw [hk] at hr h35
    have hk4 : k = 4 := by
      have h1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hr
      have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 (not_le.1 h35)
      omega
    exact h34 K₀ K ι σ₀ σ (2 ^ m) hK₀ (by rw [hK, pow_mul]) hσ₀ (fun c => by rw [hσ, pow_mul])
      h2 hpq A₀ hAI hA (by rw [hk, hk4]) hU
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega))).mp hpq
    omega
  have hp4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    omega
  rw [if_neg hp3] at hr
  obtain ⟨D₀, hc, -⟩ := h5 K₀ σ₀ (2 ^ m) hK₀ hσ₀ p hp hp5 hpq A₀ hAI hA
    ((Nat.pow_le_pow_right hp.pos (by norm_num : 4 ≤ 5)).trans hr)
  exact ⟨D₀, hc⟩

end CFSG.StandardType.TwE6FieldCore
end
