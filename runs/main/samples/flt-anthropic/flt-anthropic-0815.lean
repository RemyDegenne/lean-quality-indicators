namespace P2MW.S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

p2m_reactivate

open scoped MatrixGroups ModularForm Manifold

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup UpperHalfPlane HahnSeries

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

namespace R4GC

p2m_reactivate

p2m_reactivate

section Analytic

variable {m : ℕ} [NeZero m] {M' : ℕ}

p2m_reactivate

variable {L : Type} [Field L] [CharZero L]

variable (ι₀ : L →+* ℂ)

theorem C_eq_algebraMap (c : L) : (HahnSeries.C c : LaurentSeries L) = algebraMap L (LaurentSeries L) c := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

end Analytic
end R4GC
end
end P2MW.S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint
