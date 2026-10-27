public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

open CFSG.Open CFSG.GH74.Exceptional CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup

theorem le_E_of_normalized {Y U : Subgroup (Equiv.Perm (Fin 45))} (hYH : Y ≤ H0)
    (hY : IsPGroup 2 Y) (hUH : U ≤ H0) (hU : Nat.card U = 9)
    (hN : U ≤ normalizer (Y : Set (Equiv.Perm (Fin 45)))) : Y ≤ E := by
  set M := Y ⊔ E
  have hMH : M ≤ H0 := sup_le hYH E_le_H0
  have hMp : IsPGroup 2 M :=
    hY.to_sup_of_normal_right' isPGroup_E (hYH.trans H0_le_normalizer_E)
  have hM576 : Nat.card M ∣ 576 := card_H0 ▸ Subgroup.card_dvd_of_le hMH
  obtain ⟨n, hn⟩ := hMp.exists_card_eq
  have hEM : Nat.card E ∣ Nat.card M := Subgroup.card_dvd_of_le le_sup_right
  rw [card_E, hn] at hEM
  rw [hn] at hM576
  have hn6 : n ≤ 6 := by
    by_contra h
    have : 2 ^ 7 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := this.trans hM576
    norm_num at this
  have hn5 : 5 ≤ n := by
    by_contra h
    have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.le_of_dvd (by positivity) hEM
    omega
  rcases (show n = 5 ∨ n = 6 by omega) with rfl | rfl
  · have : M = E := (Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hn, card_E]; norm_num)).symm
    exact le_sup_left.trans this.le
  · exfalso
    have hUM : U ≤ normalizer (M : Set (Equiv.Perm (Fin 45))) := fun u hu =>
      normalizer_sup_of_le (hN hu) (H0_le_normalizer_E (hUH hu))
    have hMU : M ⊔ U = H0 := by
      apply Subgroup.eq_of_le_of_card_ge (sup_le hMH hUH)
      have h1 : Nat.card M ∣ Nat.card (M ⊔ U : Subgroup _) := Subgroup.card_dvd_of_le le_sup_left
      have h2 : Nat.card U ∣ Nat.card (M ⊔ U : Subgroup _) := Subgroup.card_dvd_of_le le_sup_right
      rw [hn] at h1
      rw [hU] at h2
      have h3 : 576 ∣ Nat.card (M ⊔ U : Subgroup _) :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
      rw [card_H0]
      exact Nat.le_of_dvd Nat.card_pos h3
    have hMn : H0 ≤ normalizer (M : Set (Equiv.Perm (Fin 45))) := by
      rw [← hMU]
      exact sup_le le_normalizer hUM
    have hMcard : Nat.card M = 2 ^ (Nat.card H0).factorization 2 := by
      rw [hn, card_H0, factorization_two_576]
    have heq : ∀ S : Subgroup (Equiv.Perm (Fin 45)), S ≤ H0 →
        Nat.card S = 2 ^ (Nat.card H0).factorization 2 → S = M := by
      intro S hSH hS
      obtain ⟨g, hg, rfl⟩ := exists_conj_eq_of_card hMH hSH hMcard hS
      ext x
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact (mem_normalizer_iff.1 (hMn hg) m).1 hm
      · intro hx
        refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        have := (mem_normalizer_iff.1 (hMn (inv_mem hg)) x).1 hx
        simpa using this
    have hk : wperm [4, 3, 1, 0] ∈ H0 := K_le_H0 (wperm_mem_gen (by simp [Kgens]))
    have h1 := heq S0 S0_le_H0 card_S0_eq
    have hc : Nat.card (S0.map (MulAut.conj (wperm [4, 3, 1, 0])).toMonoidHom) =
        2 ^ (Nat.card H0).factorization 2 := by
      rw [← card_S0_eq]
      exact Subgroup.card_map_of_injective (MulAut.conj _).injective
    have hle : S0.map (MulAut.conj (wperm [4, 3, 1, 0])).toMonoidHom ≤ H0 := by
      rintro _ ⟨s, hs, rfl⟩
      exact mul_mem (mul_mem hk (S0_le_H0 hs)) (inv_mem hk)
    have h2 := heq _ hle hc
    have hS0E : S0 ≤ E := by
      intro s hs
      have hs' : s ∈ S0.map (MulAut.conj (wperm [4, 3, 1, 0])).toMonoidHom := by
        rw [h2, ← h1]; exact hs
      have hx2 := mem_conj_S0 hs'
      obtain ⟨t, ht, hr⟩ := exists_mem_tab S0_enumOK hs
      have hm := List.all_eq_true.1 S0_meet t ht
      obtain ⟨t', ht', hr'⟩ := exists_mem_tab S0_enumOK hx2
      have hr2 : Rep ((wperm [4, 3, 1, 0])⁻¹ * s * wperm [4, 3, 1, 0])
          (tmul (tmul (wtab [4, 3, 1, 0].reverse) t) (wtab [4, 3, 1, 0])) := by
        rw [wperm_inv]
        exact rep_mul (rep_mul (rep_wperm _) hr) (rep_wperm _)
      rw [← rep_eq_tab hr' hr2] at hm
      have hc1 : S0elems.contains t' = true := List.contains_iff_mem.2 ht'
      simp only [hc1, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hm
      exact mem_gen_of_mem_tab E_enumOK hm hr
    have := Subgroup.card_le_of_le hS0E
    rw [card_S0, card_E] at this
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43
end
