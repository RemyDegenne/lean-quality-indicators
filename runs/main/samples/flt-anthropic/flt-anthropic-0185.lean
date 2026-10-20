namespace P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq

set_option autoImplicit false

p2m_open

universe u

set_option autoImplicit false

set_option autoImplicit false

open Finset BigOperators

set_option autoImplicit false

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace ModularCurve

namespace UVCrossingModel

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section BDescent

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

omit [IsAdicComplete (maximalIdeal W) W] in
theorem dvd_coeff_of_le_gNF_e (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (ab : PowerSeries W × PowerSeries W)
    (k : ℕ) (h : (k : ℕ∞) ≤ gNF e e ab) :
    ϖ ^ k ∣ PowerSeries.constantCoeff ab.1 ∧ ∀ j, ϖ ^ k ∣ PowerSeries.coeff (j + 1) ab.2 := by
  constructor
  · have h1 := h.trans (gNF_le e e ab ((0 : ℕ) : ℤ))
    rw [termOrder_natCast, zero_mul, Nat.cast_zero, add_zero, PowerSeries.coeff_zero_eq_constantCoeff] at h1
    rwa [← IsDiscreteValuationRing.addVal_le_iff_dvd, BaddVal_uniformizer_pow ϖ hϖ k]
  · intro j
    have h1 := h.trans (gNF_le e e ab (Int.negSucc j))
    rw [termOrder_negSucc, Nat.sub_self, mul_zero, Nat.cast_zero, add_zero] at h1
    rwa [← IsDiscreteValuationRing.addVal_le_iff_dvd, BaddVal_uniformizer_pow ϖ hϖ k]

end BDescent
end UVCrossingModel
end ModularCurve
end P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq
