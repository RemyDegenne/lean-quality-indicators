namespace P2MW.S_ModularForm_E4_mul_eta_pow_eight_eq

attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

p2m_open

p2m_reactivate

namespace ModularCurve

p2m_open

namespace ARails

open Complex

open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

theorem QS_S (a b c e : ℕ) (he : a + 2 * b + 4 * c = 24 * e) :
    QS ((S a b c e).map (Int.castRingHom ℂ)) (fun τ => ModularForm.eta (τ : ℂ) ^ a *
      ModularForm.eta (2 * (τ : ℂ)) ^ b * ModularForm.eta (4 * (τ : ℂ)) ^ c) := fun τ => by
  simpa [PowerSeries.coeff_map] using hasSum_etaProduct a b c e he τ

end ARails
end ModularCurve
end P2MW.S_ModularForm_E4_mul_eta_pow_eight_eq
