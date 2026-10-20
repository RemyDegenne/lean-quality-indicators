namespace P2MW.S_NumberField_FiniteSIdele_exists_addEquiv_coind_localUnits_transportUnits_apply

set_option autoImplicit false

namespace P2mS26FHF

open NumberField NumberField.PlaceTransport IsDedekindDomain

open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

section general

variable {E K : Type} [Field E] [Field K] [NumberField K] [Algebra E K]

theorem transportUnits_one {w : HeightOneSpectrum (𝓞 K)} (h : (1 : K ≃ₐ[E] K) • w = w) (u : (w.adicCompletion K)ˣ) :
    transportUnits (1 : K ≃ₐ[E] K) h u = u := by
  ext : 1
  change transport (1 : K ≃ₐ[E] K) h (u : w.adicCompletion K) = u
  rw [NumberField.PlaceTransport.transport_one E K w h]
  rfl

end general
end P2mS26FHF
end P2MW.S_NumberField_FiniteSIdele_exists_addEquiv_coind_localUnits_transportUnits_apply
