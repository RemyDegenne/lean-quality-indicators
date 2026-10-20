@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDominantRationalScheme

/-- Natural identification of a native dominant object with its round trip. -/
noncomputable def nativeCounitIso : toDenseOpen ⋙ IntegralDenseOpenRationalScheme.toNative ≅
    𝟭 IntegralDominantRationalScheme.{u} :=
  NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    change IntegralDenseOpenRationalScheme.nativeHom (denseHom f) ≫ 𝟙 Y =
      𝟙 X ≫ f
    rw [Category.comp_id]
    rw [Category.id_comp]
    exact nativeHom_denseHom f)

end IntegralDominantRationalScheme
end AlgebraicGeometry
end
