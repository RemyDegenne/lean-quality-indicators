namespace P2MW.S_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped MatrixGroups ModularForm

open UpperHalfPlane

noncomputable section

namespace P2mSolLevelOneEsymm

section Analytic

variable (p : ℕ) [hp : Fact p.Prime]

theorem qExpansion_kForm (h : ModularForm (Γ p) 2) {B : PowerSeries ℤ}
    (hB : B.map (Int.castRingHom ℂ) = qExpansion 1 ⇑h) :
    (Cser p B).map (Int.castRingHom ℂ) = qExpansion 1 ⇑(kForm p h) := by
  have hΓ := one_mem_strictPeriods_Γ p
  have hneg : ModularForm.heckeU 2 p ⇑h = -⇑(kForm p h) := by
    rw [coe_kForm, neg_neg]
  ext n
  have h1 := ModularFormClass.qCoeff_heckeU h hΓ (p_ne_zero p) n
  rw [ModularForm.coeffHeckeU_apply, ModularFormClass.qCoeff, ModularFormClass.qCoeff, hneg,
    ModularForm.qExpansion_neg one_pos hΓ (kForm p h), map_neg, ← hB, PowerSeries.coeff_map] at h1
  rw [PowerSeries.coeff_map, Cser, PowerSeries.coeff_mk, map_neg, ← h1, neg_neg]

end Analytic
end P2mSolLevelOneEsymm
end
end P2MW.S_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two
