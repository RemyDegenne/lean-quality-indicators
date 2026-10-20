namespace P2MW.S_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_coeffEmb_jq

p2m_open

open scoped MatrixGroups ModularForm Manifold

set_option autoImplicit false

noncomputable section

namespace ANb

local notation "𝒩" => niceSubalgebra

theorem A_cube_sub_B_sq : ψ 𝔞 ^ 3 - ψ 𝔟 ^ 2 = 1728 * ψ 𝔡 := by
  let T : ModularForm 𝒮ℒ 12 := ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)
  let U : ModularForm 𝒮ℒ 12 := ModularForm.E₆.mul ModularForm.E₆
  let Z : ModularForm 𝒮ℒ 12 := T - U
  have hZ : (Z : ℍ → ℂ) = ((𝔞 * (𝔞 * 𝔞) - 𝔟 * 𝔟 : 𝒩) : ℍ → ℂ) := by
    funext z
    show (T : ℍ → ℂ) z - (U : ℍ → ℂ) z = _
    rfl
  have hZq : qExpansion 1 (Z : ℍ → ℂ) =
      qExpansion 1 ⇑ModularForm.E₄ * (qExpansion 1 ⇑ModularForm.E₄ * qExpansion 1 ⇑ModularForm.E₄) -
        qExpansion 1 ⇑ModularForm.E₆ * qExpansion 1 ⇑ModularForm.E₆ := by
    rw [hZ, ← qexpHom_apply, map_sub, map_mul, map_mul, map_mul]
    rfl
  have h0 : ModularFormClass.qCoeff (Z : ℍ → ℂ) 0 = 0 := by
    simp only [ModularFormClass.qCoeff, hZq, map_sub, coeff_zero_mul', qA0, qB0]
    norm_num
  have h1 : ModularFormClass.qCoeff (Z : ℍ → ℂ) 1 = 1728 := by
    simp only [ModularFormClass.qCoeff, hZq, map_sub, coeff_one_mul, coeff_zero_mul', qA0, qA1, qB0, qB1]
    norm_num
  have hW := ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant Z h0
  have hZΔ : qExpansion 1 (Z : ℍ → ℂ) = PowerSeries.C 1728 * qExpansion 1 ModularForm.discriminant := by
    ext n
    rw [PowerSeries.coeff_C_mul]
    have := hW n
    have h1' := h1
    simp only [ModularFormClass.qCoeff] at this h1'
    rw [this, h1']
  have hL : ψ (𝔞 * (𝔞 * 𝔞) - 𝔟 * 𝔟) = 1728 * ψ 𝔡 := by
    rw [ψ_apply, ← hZ, hZΔ, map_mul, HahnSeries.ofPowerSeries_C, map_ofNat, ψ𝔡]
  rw [map_sub, map_mul, map_mul, map_mul] at hL
  rw [← hL]
  ring

end ANb
end
end P2MW.S_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_coeffEmb_jq
