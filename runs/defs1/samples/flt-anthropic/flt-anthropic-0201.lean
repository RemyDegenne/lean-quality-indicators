namespace P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_charpoly_coeff_zero_mul_leadingResidue_nfCoeff_sInf

set_option maxHeartbeats 1600000

set_option autoImplicit false

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

namespace ModularCurve

namespace UVCrossingModel

p2m_open

open IsLocalRing

section ShiftDefs

variable {W : Type u} [CommRing W]

noncomputable def nfV (π : W) (ab : PowerSeries W × PowerSeries W) : PowerSeries W × PowerSeries W :=
  (PowerSeries.C π * PowerSeries.mk fun i => PowerSeries.coeff (i + 1) ab.1,
    PowerSeries.X * (PowerSeries.C (PowerSeries.constantCoeff ab.1) + ab.2))

end ShiftDefs
end UVCrossingModel
end ModularCurve
end P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_charpoly_coeff_zero_mul_leadingResidue_nfCoeff_sInf
