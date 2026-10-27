public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.RankThree.PartOne.CTP CFSG.DihedralBlueprint

open scoped commutatorElement

variable {K : Type} [Field K] {σ : K →+* K}

theorem posUnipotent_le_normalizer_Qt :
    posUnipotent (twistedDatum σ) ≤ Subgroup.normalizer (Qt σ : Set (twistedGroup σ)) := by
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨hγR, hγp⟩ := hγ
  have hγR' : IsRoot .G2 γ := by
    rw [twistedDatum_roots] at hγR
    exact hγR
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγR'
  have hk' : k < 12 := by simpa [len_roots] using hk
  have hkp := ht_pos_aux k hk' hγp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hkp
  show twistedRootGroup σ (rt k) ≤ _
  rcases hkp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (rootGroup_le_Qt (by simp [qT])).trans Subgroup.le_normalizer
  · exact fun x hx => Xalpha_mem_normalizer_Qt hx
  · exact (rootGroup_le_Qt (by simp [qT])).trans Subgroup.le_normalizer
  · exact (rootGroup_le_Qt (by simp [qT])).trans Subgroup.le_normalizer
  · exact (rootGroup_le_Qt (by simp [qT])).trans Subgroup.le_normalizer
  · exact (rootGroup_le_Qt (by simp [qT])).trans Subgroup.le_normalizer

end CFSG.RankThree.PartOne.SEITZ7
end
