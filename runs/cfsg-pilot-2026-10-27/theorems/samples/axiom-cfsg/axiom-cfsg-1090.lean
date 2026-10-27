public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open F4Pilot (normalizerMulAut)

section Ambient

variable {G : Type*} [Group G] [Finite G] {G₀ : Subgroup G}

theorem exists_normal_index_two_of_E8_odd (hZ : Odd (Nat.card (centralizer (G₀ : Set G))))
    {n : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2 ^ n) (e : G₀ ≃* adjointGroup .E8 K)
    {t : G} (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2) (htG : t ∉ G₀)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK
  have : Finite (adjointGroup .E8 K) := by
    have : Finite (ModGL Tag.E8 K) := finite_modGL
    infer_instance
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  obtain ⟨hcyc, hCInn, hNF⟩ := e8_entrywise_complement hn hK
  have hker : Odd (Nat.card (normalizerMulAut e).ker) := by
    rw [EPilot.card_ker_normalizerMulAut]
    exact hZ
  have hout := EPilot.normalizerMulAut_not_mem_range_of_odd hZ e htN ht2 htG
  exact EPilot.exists_normal_index_two_of_action_complement_of_isConj (normalizerMulAut e) hker
    (C := (entrywiseAdjointAutHom (τ := .E8) (K := K)).range) hCInn hNF
    (EPilot.exists_normalizerMulAut_eq_conj e) htN ht hout huniq
    (exists_conj_mem_range_entrywise_of_outer_E8 hn hK (EPilot.action_sq_eq_one _ htN ht2) hout)

end Ambient
end CFSG.SeitzReduction.E8Pilot
end
