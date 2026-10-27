namespace P2MW.S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem

open UpperHalfPlane

open scoped MatrixGroups

namespace A2LevelOneCrit

noncomputable def B (N i : ℕ) : PowerSeries ℂ :=
  (PowerSeries.X ^ (N - i) * cInt N i).map (Int.castRingHom ℂ)

end A2LevelOneCrit
end P2MW.S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem
