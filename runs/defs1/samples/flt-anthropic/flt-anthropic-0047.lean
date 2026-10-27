namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_three_qExpansion_eq_cuspPoint

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_reactivate

p2m_reactivate

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries

open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ}

p2m_reactivate

section QExp

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

end QExp
end W1xLA
end
end P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_three_qExpansion_eq_cuspPoint
