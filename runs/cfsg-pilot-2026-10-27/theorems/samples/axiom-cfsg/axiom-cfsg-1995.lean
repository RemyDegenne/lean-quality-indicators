public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model

open CFSG.BenderSuzuki.External

open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

theorem torusAut_range_le_normalizer_map_conj :
    (torusAut J hJ).range ≤
      Subgroup.normalizer
        (((rootGroup J hJ).map (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →*
          MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) :
          Set (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  rintro α ⟨c, rfl⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro x hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
    change MulAut.conj (torusAut J hJ c) (MulAut.conj r) = x at hxy
    rw [← hxy, conj_conj_mulAut]
    exact Subgroup.mem_map_of_mem _ (torusAut_mem_rootGroup J hJ c hr)
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨MulAut.conj ((torusAut J hJ c)⁻¹ r),
      Subgroup.mem_map_of_mem _ ?_, ?_⟩
    · rw [← map_inv]
      exact torusAut_mem_rootGroup J hJ c⁻¹ hr
    · change MulAut.conj (torusAut J hJ c) (MulAut.conj ((torusAut J hJ c)⁻¹ r)) =
        MulAut.conj r
      rw [conj_conj_mulAut]
      simp

end
end CFSG.AGLEmbedding.UnitaryModel
end
