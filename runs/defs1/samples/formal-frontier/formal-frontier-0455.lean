@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDominantRationalSchemeOver

/-- Natural quotient-identity comparison with the native dominant round trip. -/
noncomputable def nativeCounitIso {S : Scheme.{u}} :
    toDenseOpen ⋙ IntegralDenseOpenRationalSchemeOver.toNative ≅
      𝟭 (IntegralDominantRationalSchemeOver S) :=
  NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    change IntegralDenseOpenRationalSchemeOver.nativeHom (denseHom f) ≫ 𝟙 Y = 𝟙 X ≫ f
    rw [Category.comp_id, Category.id_comp]
    exact nativeHom_denseHom f)

end IntegralDominantRationalSchemeOver
end AlgebraicGeometry
end
