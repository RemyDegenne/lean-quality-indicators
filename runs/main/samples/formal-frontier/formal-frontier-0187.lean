public section

noncomputable section

open QuadraticAlgebra

namespace QuadraticAlgebra

theorem not_isPrincipal_sqrtNegFiveRingOfIntegersIdealTwo :
    ¬ Submodule.IsPrincipal sqrtNegFiveRingOfIntegersIdealTwo := by
  intro hprincipal
  have hmapped := hprincipal.map_ringHom
    sqrtNegFiveRingOfIntegersEquiv.symm.toRingHom
  have hmap :
      sqrtNegFiveRingOfIntegersIdealTwo.map
          sqrtNegFiveRingOfIntegersEquiv.symm.toRingHom =
        sqrtNegFiveRingOfIntegersIdealTwo.comap
          sqrtNegFiveRingOfIntegersEquiv.toRingHom :=
    Ideal.map_symm sqrtNegFiveRingOfIntegersEquiv
  rw [hmap, comap_sqrtNegFiveRingOfIntegersIdealTwo] at hmapped
  exact not_isPrincipal_sqrtNegFiveIdealTwo hmapped

end QuadraticAlgebra
end
end
