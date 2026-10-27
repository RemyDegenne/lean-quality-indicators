public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

open CFSG.GorensteinWalter CFSG.Glauberman.Dickson

variable {G : Type} [Group G] [Finite G]

open Borel5 in
theorem Frame5.nonempty
    (s : Std G) : Nonempty (Frame5 s) := by
  obtain ⟨e', P₀, hT⟩ := s.fr.exists_coords
  set F := GaloisField s.p s.f
  set ι := psl2Emb e'
  have hι : Function.Injective ι := PSL2Sub.emb_injective e'
  have hF2 : ringChar F ≠ 2 := by
    rw [ringChar.eq F s.p]
    exact s.p_ne_two
  have hcardF : Nat.card F = s.q := GaloisField.card s.p s.f s.f_pos.ne'
  have hE : ∀ g ∈ s.fr.E, ∃ σ : F ≃+* F, ∀ y, g * ι y * g⁻¹ = ι (psl2FieldAut F σ y) :=
    fun g hg => s.fr.conj_eq_fieldAut hT hg
  have hnorm : ∀ H : Subgroup PSL(2, F), (∀ σ : F ≃+* F, ∀ y ∈ H, psl2FieldAut F σ y ∈ H) →
      s.fr.E ≤ Subgroup.normalizer ((H.map ι : Subgroup G) : Set G) := by
    intro H hH g hg
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨σ, hσ⟩ := hE g hg
      exact ⟨_, hH σ y hy, (hσ y).symm⟩
    · rintro ⟨y, hy, hyz⟩
      obtain ⟨σ, hσ⟩ := hE g⁻¹ (s.fr.E.inv_mem hg)
      have hz : z = g⁻¹ * ι y * g⁻¹⁻¹ := by
        change ι y = g * z * g⁻¹ at hyz
        rw [hyz]
        group
      rw [hz, hσ y]
      exact ⟨_, hH σ y hy, rfl⟩
  have hmapN : ∀ H : Subgroup PSL(2, F), H ≤ Subgroup.normalizer (unip F : Set PSL(2, F)) →
      H.map ι ≤ Subgroup.normalizer (((unip F).map ι : Subgroup G) : Set G) := by
    intro H hH
    have h1 := JT.map_normalizer_of_injective ι hι (unip F)
    exact (Subgroup.map_mono hH).trans (h1.le.trans inf_le_right)
  have hEN : s.fr.E ≤ Subgroup.normalizer (((unip F).map ι : Subgroup G) : Set G) :=
    hnorm _ fun σ _ hy => fieldAut_mem_unip σ hy
  refine ⟨{
    B := (torus F).map ι
    B_le := PSL2Sub.map_le e' _
    B_cyclic := ?_
    card_B := ?_
    E_le_normalizer_B := hnorm _ fun σ _ hy => fieldAut_mem_torus σ hy
    P₁ := (unip F).map ι
    P₁_le := PSL2Sub.map_le e' _
    card_P₁ := ?_
    B_le_normalizer := sup_le (hmapN _ torus_le_normalizer_unip) hEN
    fixedPointFree := ?_
    normalizer_eq := ?_ }⟩
  · have := isCyclic_torus (F := F)
    exact isCyclic_of_surjective ((torus F).equivMapOfInjective ι hι)
      ((torus F).equivMapOfInjective ι hι).surjective
  · rw [Subgroup.card_map_of_injective hι, card_torus hF2, hcardF]
  · rw [Subgroup.card_map_of_injective hι, psl2UpperUnipotentSubgroup_card, hcardF]
  · rintro _ ⟨t, ht, rfl⟩ ht1
    have ht1' : t ≠ 1 := by
      rintro rfl
      exact ht1 (map_one ι)
    have h0 := unip_inf_centralizer_torus ht ht1'
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨⟨u, hu, rfl⟩, hzc⟩ := Subgroup.mem_inf.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hzc
    have hut : u ∈ unip F ⊓ Subgroup.centralizer ({t} : Set PSL(2, F)) :=
      ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr (hι hzc)⟩
    rw [h0, Subgroup.mem_bot] at hut
    rw [hut, map_one, Subgroup.mem_bot]
  · apply le_antisymm
    · rintro x ⟨hxN, hxKE⟩
      obtain ⟨k, hk, e, he, rfl⟩ :=
        (mem_sup_iff_of_le_normalizer s.fr.E_le_normalizer_K).mp hxKE
      have hkN : k ∈ Subgroup.normalizer (((unip F).map ι : Subgroup G) : Set G) := by
        have := mul_mem hxN (hEN (s.fr.E.inv_mem he))
        rwa [mul_inv_cancel_right] at this
      obtain ⟨y, rfl⟩ := PSL2Sub.exists_emb_eq e' hk
      have hyN : ι y ∈ (Subgroup.normalizer (unip F : Set PSL(2, F))).map ι := by
        rw [JT.map_normalizer_of_injective ι hι]
        exact ⟨⟨y, rfl⟩, hkN⟩
      rw [Subgroup.mem_map_iff_mem hι, normalizer_unip] at hyN
      have hk' : ι y ∈ (unip F).map ι ⊔ (torus F).map ι := by
        rw [← Subgroup.map_sup]
        exact Subgroup.mem_map_of_mem ι hyN
      exact mul_mem (Subgroup.mem_sup_left hk') (Subgroup.mem_sup_right he)
    · refine le_inf (sup_le (sup_le Subgroup.le_normalizer
        (hmapN _ torus_le_normalizer_unip)) hEN) (sup_le (sup_le ?_ ?_) le_sup_right)
      · exact (PSL2Sub.map_le e' _).trans le_sup_left
      · exact (PSL2Sub.map_le e' _).trans le_sup_left

end CFSG.Walter.W67
end
