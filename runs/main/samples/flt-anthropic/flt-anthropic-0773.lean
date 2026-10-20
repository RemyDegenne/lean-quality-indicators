namespace P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul

set_option autoImplicit false

open scoped MatrixGroups ModularForm

p2m_reactivate

namespace Conj6

open ModularCurve

section Qc

theorem Qc_eq_zero_iff {N : ℕ} {k : ℤ} (F : ModularForm (Γ1 N) k) : Qc (⇑F : UpperHalfPlane → ℂ) = 0 ↔ F = 0 := by
  rw [Qc, map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective,
    ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_Γ1 F]

end Qc
end Conj6
end P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul
