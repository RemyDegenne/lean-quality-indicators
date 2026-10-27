public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalGroups.UnitaryFlag

open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock spEmbed)

theorem ggSecFiveBPermUniSpChartInput_of_mp (hMp : GGInnerDiagMpInput) :
    GGSecFiveBPermUniSpChartInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n _ _ h5 eta _ hAfull _ _ _ f K i0 hf hcell
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 3 := ⟨n - 3, by omega⟩
  obtain ⟨y, hyBs, hKc, π, _, ⟨κ, ζ, hκ⟩, _, _, _, _, _, hUF, hLF⟩ :=
    GGSecFiveBPermUniSpCell.exists_frames hMp hR (r := s + 1) (by omega) hAfull (by omega)
      (fun h => absurd h (by omega)) hcell
  have hF4 : 4 ≤ Nat.card (GaloisField 2 f) := TagsExc.four_le_card_galoisField hf
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  have h01 : π 0 ≠ π 1 := π.injective.ne (Fin.ne_of_val_ne (by simp))
  have h03 : π 0 ≠ π 3 := π.injective.ne (Fin.ne_of_val_ne (by
    rw [Fin.val_zero]
    show 0 ≠ 3 % (s + 1 + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
    omega))
  obtain ⟨g, hgL, hg, hgη⟩ := exists_mem_conjAut_eq_permAut_swap hAfull h01
  obtain ⟨w, -, hw, hwη⟩ := exists_mem_conjAut_eq_permAut_swap hAfull h03
  obtain ⟨κ₂, hκ₂, hκ₂r, hov, hlong, hcross⟩ :=
    ggSecFiveBPermZeta_overlap_of_swap (s := s) hp2 hF4 (by omega) hBsC hyBs hKc hκ hg hgη hw hwη
  obtain ⟨κ₂', hκ₂', hκ₂'r, hsh, hlo, hc1, hc2⟩ :=
    CFSG.ClassicalInvolution.WeakCT.exists_spSpCharts_of_overlap (s := s) (by omega) hκ.1 hκ₂
      hov hlong hcross
  have hMK : ∀ c d : Fin (s + 3), c ≠ d → c ≠ π 0 → d ≠ π 0 →
      ggBlockComm Bs eta {c, d} ≤ K := by
    intro c d hcd hc hd
    have ha : π.symm c ≠ 0 := fun h => hc (by rw [← h, Equiv.apply_symm_apply])
    have hb : π.symm d ≠ 0 := fun h => hd (by rw [← h, Equiv.apply_symm_apply])
    let τ : Fin 2 → Fin (s + 2) := ![(π.symm c).pred ha, (π.symm d).pred hb]
    have h0 : π (τ 0).succ = c := by simp [τ]
    have h1 : π (τ 1).succ = d := by simp [τ]
    have hne : τ 0 ≠ τ 1 := fun h => hcd (by rw [← h0, ← h1, h])
    have hτ : Function.Injective τ := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd hij hne
      · exact absurd hij.symm hne
      · rfl
    have hτs : ¬ Function.Surjective τ := by
      intro h
      have := Fintype.card_le_of_surjective τ h
      simp only [Fintype.card_fin] at this
      omega
    have hset : (Set.range fun l => π (τ l).succ) = ({c, d} : Set (Fin (s + 3))) := by
      ext z
      simp only [Set.mem_range, Fin.exists_fin_two, h0, h1, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
    rw [← hset, ggSecFiveBPermZeta_commutator_centralizer_eq hp2 hF4 hBsC hyBs hKc hκ τ hτ hτs]
    rw [MonoidHom.range_comp]
    exact (Subgroup.map_le_range _ _).trans hκ.2.1.le
  have hjoin : K ⊔ K.map (MulAut.conj g).toMonoidHom = L ⊔ K :=
    hLF.sup_map_conj_eq hUF hf hp (by omega) h01 hgL hg hgη hMK
  refine ⟨s, rfl, κ, κ₂', hκ.1, hκ₂', ?_, hsh, hlo, hc1, hc2⟩
  rw [hκ.2.1, hκ₂'r, hκ₂r, hjoin]

end CFSG.StandardType
end
