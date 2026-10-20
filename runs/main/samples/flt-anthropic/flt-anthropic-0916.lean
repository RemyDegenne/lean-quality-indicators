namespace P2MW.S_ModularCurve_UVCrossingModel_exists_mul_eq_pow_mul_and_maximalIdeal_eq_span_of_ringEquiv_adicCompletion_pow

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 12800000

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel TensorProduct

namespace L1BUV

section Crossing

variable {W : Type} [CommRing W] [IsLocalRing W] (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (w : ℕ) (hw : 1 ≤ w)

include hπ hw in
theorem brQuot_mk (f : MvPowerSeries (Fin 2) W) :
    brQuot π hπ w hw (UVCrossingModel.mk (π ^ w) f) = brHom (IsLocalRing.residue W) f := rfl

end Crossing
end L1BUV
end P2MW.S_ModularCurve_UVCrossingModel_exists_mul_eq_pow_mul_and_maximalIdeal_eq_span_of_ringEquiv_adicCompletion_pow
