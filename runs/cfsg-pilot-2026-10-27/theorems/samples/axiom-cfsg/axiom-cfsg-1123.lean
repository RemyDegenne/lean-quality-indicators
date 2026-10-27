public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.LU24 CFSG.Quasithin.H.LU CFSG.Monster.Code
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Open CFSG.Quasithin.H.Coc

theorem commV_imgCd_sxP0 : CFSG.Quasithin.commV (imgCd sxP0) = V10 := by
  have hmono : imgCd sxP0 ≤ imgCd sxGen :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono AutPerm sxP0_le_gen)
  have hgen1 : ∀ m, toW 11 (actM sxG1C m ^^^ m) ∈ CFSG.Quasithin.commV (imgCd sxP0) :=
    fun m => toW_comm_mem_commV sxG1C m
      ⟨rhoCd sxG1_mem, rhoCd_mem_imgCd sxG1_mem sxG1_mem_P0, actsBy_sxG1⟩
  have hgen2 : ∀ m, toW 11 (actM sxG2C m ^^^ m) ∈ CFSG.Quasithin.commV (imgCd sxP0) :=
    fun m => toW_comm_mem_commV sxG2C m
      ⟨rhoCd sxG2_mem, rhoCd_mem_imgCd sxG2_mem sxG2_mem_P0, actsBy_sxG2⟩
  refine le_antisymm ?_ ?_
  · change Subgroup.closure {w : W11 | ∃ x ∈ imgCd sxP0, ∃ v : W11, x v * v⁻¹ = w} ≤ V10
    rw [Subgroup.closure_le]
    rintro w ⟨φ, hφ, v, rfl⟩
    exact imgCd_sxGen_comm_mem_V10 φ (hmono hφ) v
  · intro v hv
    obtain ⟨m, hm, rfl⟩ := hv
    have hmem : ∀ a ∈ v10Basis, toW 11 a ∈ CFSG.Quasithin.commV (imgCd sxP0) := by
      intro a ha
      rw [v10Basis_comm] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hgen1 1
      · exact hgen1 2
      · exact hgen1 4
      · exact hgen1 8
      · exact hgen1 16
      · exact hgen1 32
      · exact hgen1 128
      · exact hgen1 256
      · exact hgen2 1
      · exact hgen2 16
    exact mem_of_combos (fun x => toW 11 x ∈ CFSG.Quasithin.commV (imgCd sxP0))
      (by rw [toW_zero]; exact (CFSG.Quasithin.commV (imgCd sxP0)).one_mem)
      (fun a b ha hb => by rw [toW_xor]; exact (CFSG.Quasithin.commV (imgCd sxP0)).mul_mem ha hb)
      v10Basis hmem m hm

end CFSG.ASVolI.H16
end
