namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace W1xLA

variable (m : ℕ) [NeZero m]

def Dr : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(m : ℝ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [mne m])

end W1xLA
end
end P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0
