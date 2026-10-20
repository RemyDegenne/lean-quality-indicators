namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_arithFrobC_pow_smul_residueFst_eq_of_isFrobeniusAt_of_coe_mem_fieldOver

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

open scoped Pointwise

namespace PressResFrob

theorem redRes_coeffMap (M : ℕ) [NeZero M] (A : ValuationSubring (AlgebraicClosure ℚ)) {k : Type*} [Field k]
    (red : A →+* k) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : ∀ a ∈ A, σ a ∈ A)
    (τ : k →+* k) (hred : ∀ a : A, red ⟨σ a, hσ a a.2⟩ = τ (red a))
    (r : ↥(CharPReduction.modularRing M A.toSubring)) :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing M A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs M A.toSubring)
        ⟨coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) r, coeffMap_mem_modularRing M A σ hσ r.2⟩ =
      coeffMap τ (CharPReduction.redRes A.toSubring red (CharPReduction.modularRing M A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs M A.toSubring) r) := by
  ext n
  rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff, CharPReduction.redRes_apply]
  conv_rhs => rw [coeffMap_coeff, CharPReduction.coeffRed_coeff, ← hred]
  congr 1

end PressResFrob
end P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_arithFrobC_pow_smul_residueFst_eq_of_isFrobeniusAt_of_coe_mem_fieldOver
