public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent

section Map

variable {X X' : Type} [Group X] [Group X']

theorem SevenNineConfig.map {L S Y Z : Subgroup X} {p : ℕ} (h : SevenNineConfig L S p Y Z)
    (φ : X →* X') (hY : Y ⊓ φ.ker = ⊥) (hS : S ⊓ φ.ker = ⊥) :
    SevenNineConfig (L.map φ) (S.map φ) p (Y.map φ) (Z.map φ) := by
  have hZY : Z ≤ Y := by
    rw [h.z_eq]
    exact inf_le_left
  have hZ : Z ⊓ φ.ker = ⊥ := eq_bot_mono (inf_le_inf_right _ hZY) hY
  refine
    { prime := h.prime
      ne_two := h.ne_two
      card_s := (CFSG.card_map_eq_card_of_inf_ker_eq_bot φ hS).trans h.card_s
      le := Subgroup.map_mono h.le
      elemAbelian := h.elemAbelian.map φ
      s_le := (Subgroup.map_mono h.s_le).trans (Subgroup.le_normalizer_map φ)
      z_eq := ?_
      card_z := ?_
      z_le := ?_
      exists_conj := ?_ }
  · refine le_antisymm (le_inf (Subgroup.map_mono hZY) ?_) ?_
    · calc Z.map φ ≤ (Subgroup.centralizer (S : Set X)).map φ := by
            refine Subgroup.map_mono ?_
            rw [h.z_eq]
            exact inf_le_right
        _ ≤ Subgroup.centralizer (φ '' (S : Set X)) :=
            Subgroup.map_centralizer_le_centralizer_image _ φ
        _ = Subgroup.centralizer ((S.map φ : Subgroup X') : Set X') := by
            rw [Subgroup.coe_map]
    · rintro _ ⟨⟨y, hy, rfl⟩, hc⟩
      refine Subgroup.mem_map_of_mem φ ?_
      rw [h.z_eq]
      refine ⟨hy, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      have hcs : φ s * φ y = φ y * φ s :=
        Subgroup.mem_centralizer_iff.mp hc (φ s) (Subgroup.mem_map_of_mem φ hs)
      have h1 : s * y⁻¹ * s⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (h.s_le hs) y⁻¹).mp (Y.inv_mem hy)
      have hmem : y * (s * y⁻¹ * s⁻¹) ∈ Y ⊓ φ.ker := Subgroup.mem_inf.mpr ⟨Y.mul_mem hy h1, by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← mul_assoc,
          ← mul_assoc, ← hcs]
        group⟩
      rw [hY, Subgroup.mem_bot] at hmem
      calc s * y = (y * (s * y⁻¹ * s⁻¹))⁻¹ * y * s := by group
        _ = y * s := by rw [hmem, inv_one, one_mul]
  · rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot φ hZ, CFSG.card_map_eq_card_of_inf_ker_eq_bot φ hY]
    exact h.card_z
  · refine (Subgroup.map_mono h.z_le).trans ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun g => iSup_le fun hg => iSup_le fun h2 => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← map_conjSubgroup_hom]
    have h2' : IsPGroup 2 ↥(S.map φ ⊔ conjSubgroup (S.map φ) (φ g)) := by
      rw [map_conjSubgroup_hom, ← Subgroup.map_sup]
      exact h2.map φ
    exact le_iSup_of_le (φ g) (le_iSup_of_le (Subgroup.mem_map_of_mem φ hg)
      (le_iSup_of_le h2' le_rfl))
  · intro B' hB'Y hB'card
    have hBY : Y ⊓ B'.comap φ ≤ Y := inf_le_left
    have hBmap : (Y ⊓ B'.comap φ).map φ = B' := by
      refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_right) fun b hb => ?_
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (hB'Y hb)
      exact Subgroup.mem_map_of_mem φ ⟨hy, hb⟩
    have hBk : (Y ⊓ B'.comap φ) ⊓ φ.ker = ⊥ := eq_bot_mono (inf_le_inf_right _ hBY) hY
    have hBcard : Nat.card ↥(Y ⊓ B'.comap φ) * p = Nat.card Y := by
      rw [← CFSG.card_map_eq_card_of_inf_ker_eq_bot φ hBk, hBmap, hB'card,
        CFSG.card_map_eq_card_of_inf_ker_eq_bot φ hY]
    obtain ⟨g, hgL, hgN, hne, hnle⟩ := h.exists_conj _ hBY hBcard
    have hgY : conjSubgroup (Y ⊓ B'.comap φ) g ≤ Y := fun x hx => by
      rw [mem_conjSubgroup_iff] at hx
      exact (Subgroup.mem_normalizer_iff.mp hgN x).mpr (hBY hx)
    refine ⟨φ g, Subgroup.mem_map_of_mem φ hgL,
      Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ hgN), ?_, ?_⟩
    · rw [← hBmap, map_conjSubgroup_hom]
      intro heq
      exact hne (le_antisymm (le_of_map_le φ hY hgY hZY heq.le)
        (le_of_map_le φ hY hZY hgY heq.ge))
    · rw [← hBmap, map_conjSubgroup_hom, ← Subgroup.map_commutator]
      exact fun hle => hnle (le_of_map_le φ hY (commutator_le_of_le_normalizer h.s_le) hgY hle)

end Map
end CFSG.LocalAnalysis.WeakClosure81
end
