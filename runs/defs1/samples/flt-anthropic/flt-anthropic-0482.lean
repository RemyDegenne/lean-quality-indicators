namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries

open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {L : Type} [Field L] [CharZero L]

section Emb

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

end Emb
end W1xLA
end
end P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
