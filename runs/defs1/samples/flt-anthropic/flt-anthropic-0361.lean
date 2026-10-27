namespace P2MW.S_ModularCurve_coeff_jNum_le_twelve

set_option autoImplicit false

open PowerSeries

open scoped PowerSeries.WithPiTopology

namespace ModularCurve

p2m_open

namespace JCoeff

variable {R : Type*} [CommRing R]

def LowCoeffs (f : R⟦X⟧) (L : List R) : Prop :=
  ∀ i : ℕ, i < L.length → coeff i f = L.getD i 0

end JCoeff
end ModularCurve
end P2MW.S_ModularCurve_coeff_jNum_le_twelve
