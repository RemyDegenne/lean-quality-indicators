public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {G : Type*} [Group G]

theorem IsWreath.isRegFam [Finite G] {X A L N C : Subgroup G} (hW : IsWreath (X ⊔ A) L A N C)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hcop : Nat.Coprime (Nat.card A) (Nat.card X))
    (hLX : L ≤ X) (hL1 : L ≠ ⊥) :
    IsRegFam A X {Y | ∃ a ∈ A, Y = L.map (MulAut.conj a).toMonoidHom} N := by
  have := hW.isMulCommutative
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hWX : X ⊔ A ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hAX
  set M : Subgroup G := ⨆ g ∈ X ⊔ A, L.map (MulAut.conj g).toMonoidHom with hM
  have hMX : M ≤ X := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hWX hg) l).mp (hLX hl)
  have hWM : X ⊔ A ≤ Subgroup.normalizer (M : Set G) := by
    refine Near.Thm210.le_normalizer_of_conj_mem fun c hc x hx => ?_
    have hle : M ≤ M.comap (MulAut.conj c).toMonoidHom := by
      refine iSup₂_le fun g hg => ?_
      rw [← Subgroup.map_le_iff_le_comap, Near.Thm210.map_conj_map_conj]
      exact le_iSup₂_of_le (c * g) (mul_mem hc hg) le_rfl
    simpa using hle hx
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := le_sup_right.trans hWM
  have hLM : L ≤ M := by
    refine le_trans (Near.Thm210.map_conj_one L).symm.le ?_
    exact le_iSup₂_of_le (1 : G) (one_mem (X ⊔ A)) le_rfl
  have hXA : X ⊓ A = ⊥ := by
    have h1 : Nat.card ↥(X ⊓ A) ∣ Nat.card A := Subgroup.card_dvd_of_le inf_le_right
    have h2 : Nat.card ↥(X ⊓ A) ∣ Nat.card X := Subgroup.card_dvd_of_le inf_le_left
    have h3 := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one, Nat.dvd_one] at h3
    exact Subgroup.eq_bot_of_card_eq _ h3
  have hXM : X ≤ M := by
    intro x hx
    have hxW : x ∈ M ⊔ A := by
      have h1 : x ∈ L ⊔ A := hW.sup_eq ▸ Subgroup.mem_sup_left hx
      exact sup_le_sup_right hLM A h1
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left M A hAM] at hxW
    obtain ⟨m, hm, a, ha, rfl⟩ := hxW
    have haX : a ∈ X ⊓ A :=
      Subgroup.mem_inf.mpr ⟨by simpa using mul_mem (inv_mem (hMX hm)) hx, ha⟩
    rw [hXA, Subgroup.mem_bot] at haX
    rw [haX]
    simpa using hm
  have hMeq : M = X := le_antisymm hMX hXM
  have hdp : IsDirectProduct {K | ∃ g ∈ X ⊔ A, K = L.map (MulAut.conj g).toMonoidHom} M :=
    hW.isDirectProduct
  have hset : {K | ∃ g ∈ X ⊔ A, K = L.map (MulAut.conj g).toMonoidHom} =
      {Y | ∃ a ∈ A, Y = L.map (MulAut.conj a).toMonoidHom} := by
    ext K
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left X A hAX] at hg
      obtain ⟨x, hxX, a, haA, rfl⟩ := hg
      refine ⟨a, haA, ?_⟩
      have hJ : L.map (MulAut.conj a).toMonoidHom ∈
          {K | ∃ g ∈ X ⊔ A, K = L.map (MulAut.conj g).toMonoidHom} :=
        ⟨a, Subgroup.mem_sup_right haA, rfl⟩
      have h1 : (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj x).toMonoidHom =
          L.map (MulAut.conj a).toMonoidHom :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hdp.le_normalizer hJ (hMeq ▸ hxX))
      rw [← h1, Near.Thm210.map_conj_map_conj]
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, Subgroup.mem_sup_right ha, rfl⟩
  have hdp' : IsDirectProduct {Y | ∃ a ∈ A, Y = L.map (MulAut.conj a).toMonoidHom} X := by
    have h := hdp
    rw [hMeq, hset] at h
    exact h
  refine ⟨hdp', ⟨L, 1, one_mem A, (Near.Thm210.map_conj_one L).symm⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ h
    exact hL1 ((Subgroup.map_eq_bot_iff_of_injective L (MulAut.conj a).injective).mp h)
  · rintro a ha _ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, Near.Thm210.map_conj_map_conj L b a⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨b * a⁻¹, mul_mem hb (inv_mem ha), ?_⟩
    rw [Near.Thm210.map_conj_map_conj, inv_mul_cancel_right]
  · rintro _ ⟨a, ha, rfl⟩
    rw [hW.N_eq]
    ext b
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    refine and_congr_right fun hb => ?_
    exact Near.Lemma212.mem_normalizer_map_conj_iff_of_commute (hcomm b hb a ha)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
end
