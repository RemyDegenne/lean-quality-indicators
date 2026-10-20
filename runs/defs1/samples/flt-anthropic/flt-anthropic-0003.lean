namespace P2MW.S_NumberField_PlaceTransport_exists_equiv_placesAbove_sigma_quotient_decomp_above

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

p2m_open

open scoped Classical NumberField.LevelArith NumberField.PlaceTransport

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 1600000

set_option Elab.async false

p2m_open

open scoped Classical NumberField.LevelArith NumberField.PlaceTransport NumberField Pointwise

namespace OrbitStabFin

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
  (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E)))

local notation "G" => (K ≃ₐ[E] K)

noncomputable def underS : ↥(NumberField.SUnits.placesAbove E K S) → ↥S := fun w => ⟨w.1.under (𝓞 E), w.2⟩

end OrbitStabFin
end P2MW.S_NumberField_PlaceTransport_exists_equiv_placesAbove_sigma_quotient_decomp_above
