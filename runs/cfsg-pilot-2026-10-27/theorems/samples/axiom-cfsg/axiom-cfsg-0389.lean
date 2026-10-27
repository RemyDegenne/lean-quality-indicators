public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem tcjOrth_innDiagAllOrth_of_ggLabelRigidInput (hRig : GGLabelRigidInput) :
    InnDiagAllOn FamOrth := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hin hα hlabJ hJ
  obtain ⟨hmodel, a, rfl⟩ := Y10GInnOrthMark.innDiagKind_orth_data hcen hFam hin
  have hap : a ^ p = 1 := by
    have hc : a ^ p ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := DFunLike.congr_fun (show MulAut.conj (a ^ p) = 1 by rw [map_pow, hα]) z
      rw [MulAut.conj_apply, MulAut.one_apply] at hz
      exact (mul_inv_eq_iff_eq_mul.mp hz).symm
    rw [hcen] at hc
    exact Subgroup.mem_bot.mp hc
  obtain ⟨t, ht, hG⟩ : ∃ t : StatedLieTag, (t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel S t labK.rank 2 (canonLabel labK).n := by
    rcases hmodel with hG | hG
    · exact ⟨_, Or.inl rfl, hG⟩
    · exact ⟨_, Or.inr rfl, hG⟩
  rcases tcjOrth_quotCenter_canonLabel_cases_of_component_conj_omega hRig ht hG hp hp2 a hap
      ((CFSG.Assembly.isComponentOf_iff_open).mp hJ) hlabJ with
    ⟨b, k, -, hnk, hA⟩ | ⟨b, k, -, hnk, hA | hA⟩ | ⟨s, -, hB⟩ | ⟨s, hD⟩ | ⟨s, hD⟩
  ·
    simpa [hA] using hnk
  ·
    simpa [hA] using hnk
  · simpa [hA] using hnk
  ·
    simp [hB]
  ·
    simp [hD]
  ·
    simp [hD]

end CFSG.StandardType.TCJ
end
