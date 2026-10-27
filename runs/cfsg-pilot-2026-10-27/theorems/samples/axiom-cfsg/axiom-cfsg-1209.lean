public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

theorem w16l_sym_small {X : Type} [Group X] [Finite X] {B : Subgroup X} {k : ℕ}
    (hB2 : Nat.card B = 2) (hk : IsSymGp (X ⧸ CFSG.Open.fusionOddCore X) k) (hk4 : k < 4) :
    k = 2 ∧ B ⊔ CFSG.Open.fusionOddCore X = ⊤ := by
  obtain ⟨e⟩ := hk
  have hQcard : Nat.card (X ⧸ CFSG.Open.fusionOddCore X) = k.factorial := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  interval_cases k
  · exfalso
    exact w16l_false_of_fusionOddCore_index_one hB2 (by rw [hQcard]; norm_num)
  · exfalso
    exact w16l_false_of_fusionOddCore_index_one hB2 (by rw [hQcard]; norm_num)
  · refine ⟨rfl, ?_⟩
    have hQ2 : Nat.card (X ⧸ CFSG.Open.fusionOddCore X) = 2 := by
      rw [hQcard]
      norm_num
    have hOodd := w16l_odd_card_fusionOddCore X
    have hOidx : (CFSG.Open.fusionOddCore X).index = 2 := by
      rw [Subgroup.index_eq_card]
      exact hQ2
    have hBnotO : ¬ B ≤ CFSG.Open.fusionOddCore X := by
      intro hBO
      have hdvd : Nat.card B ∣ Nat.card (CFSG.Open.fusionOddCore X) :=
        Subgroup.card_dvd_of_le hBO
      rw [hB2] at hdvd
      exact hOodd.not_two_dvd_nat hdvd
    have hne : B ⊔ CFSG.Open.fusionOddCore X ≠ CFSG.Open.fusionOddCore X := by
      intro h
      exact hBnotO (le_sup_left.trans (le_of_eq h))
    exact w16l_eq_top_of_le_of_index_eq_two hOidx le_sup_right hne
  · exfalso
    have hQ6 : Nat.card (X ⧸ CFSG.Open.fusionOddCore X) = 6 := by
      rw [hQcard]
      norm_num
    have hOodd := w16l_odd_card_fusionOddCore X
    obtain ⟨T, hTnormal, _, hTindex⟩ :=
      w16l_exists_normal_card_three_of_card_six hQ6
    have hf : Function.Surjective (QuotientGroup.mk' (CFSG.Open.fusionOddCore X)) :=
      QuotientGroup.mk'_surjective _
    have hNcard : Nat.card (T.comap (QuotientGroup.mk' (CFSG.Open.fusionOddCore X))) =
        3 * Nat.card (CFSG.Open.fusionOddCore X) := by
      have h := w16l_card_comap_of_index_two_card_six
        (QuotientGroup.mk' (CFSG.Open.fusionOddCore X)) hf hQ6 hTindex
      rwa [QuotientGroup.ker_mk' (CFSG.Open.fusionOddCore X)] at h
    have hNodd : Odd (Nat.card (T.comap
        (QuotientGroup.mk' (CFSG.Open.fusionOddCore X)))) := by
      rw [hNcard]
      exact Odd.mul (by decide : Odd 3) hOodd
    haveI : (T.comap (QuotientGroup.mk' (CFSG.Open.fusionOddCore X))).Normal :=
      hTnormal.comap (QuotientGroup.mk' (CFSG.Open.fusionOddCore X))
    have hNle : T.comap (QuotientGroup.mk' (CFSG.Open.fusionOddCore X)) ≤
        CFSG.Open.fusionOddCore X := w16l_le_fusionOddCore hNodd
    have hle_card : Nat.card (T.comap (QuotientGroup.mk' (CFSG.Open.fusionOddCore X))) ≤
        Nat.card (CFSG.Open.fusionOddCore X) := Subgroup.card_le_of_le hNle
    rw [hNcard] at hle_card
    have hOpos : 0 < Nat.card (CFSG.Open.fusionOddCore X) := hOodd.pos
    omega

end CFSG.LocalAnalysis.WeakClosure81
end
