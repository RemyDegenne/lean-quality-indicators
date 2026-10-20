@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDominantRationalSchemeOver

/-- The native-to-controlled conversion commutes with forgetting to the
existing absolute integral dense-open category. -/
noncomputable def forgetDenseOpenIso {S : Scheme.{u}} :
    forget (S := S) ⋙ IntegralDominantRationalScheme.toDenseOpen ≅
      toDenseOpen ⋙ IntegralDenseOpenRationalSchemeOver.forget :=
  NatIso.ofComponents (fun X => Iso.refl _) (by
    intro X Y f
    change IntegralDominantRationalScheme.denseHom ((forget (S := S)).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (IntegralDenseOpenRationalSchemeOver.forget (S := S)).map (denseHom f)
    rw [Category.comp_id, Category.id_comp]
    apply ObjectProperty.hom_ext
    apply DenseOpenRationalScheme.hom_ext
    rfl)

end IntegralDominantRationalSchemeOver
end AlgebraicGeometry
end
