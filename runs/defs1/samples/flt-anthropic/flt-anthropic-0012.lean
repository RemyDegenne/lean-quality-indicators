namespace P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply

set_option autoImplicit false

p2m_reactivate

namespace SIdeleRealisation

set_option synthInstance.maxHeartbeats 800000

open IsDedekindDomain NumberField

open scoped NumberField.PlaceTransport NumberField.PlaceDecomp NumberField.InfPlaceDecomp

section main2

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]

variable {S : Finset (HeightOneSpectrum (𝓞 E))}

noncomputable def pre (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : u ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}) : NumberField.SIdele.obj E K S :=
  fun i => match i with
  | Sum.inl (Sum.inl v) => (eU E K v.1).symm (Additive.ofMul fun w => finUnitAt w.1 (finPartOf u))
  | Sum.inl (Sum.inr v) => (eI E K v.1).symm (Additive.ofMul fun w =>
      unitOfMem (finUnitAt w.1 (finPartOf u)) (mem_and_mem hu w.1 (fun h => v.2 (w.2 ▸ h))).1
        (mem_and_mem hu w.1 (fun h => v.2 (w.2 ▸ h))).2)
  | Sum.inr v => (eA E K v).symm (Additive.ofMul fun w => infPartOf u w.1)

end main2
end SIdeleRealisation
end P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply
