@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDenseOpenRationalScheme

/-- Natural identification of an integral dense-open object with its round trip. -/
noncomputable def nativeUnitIso : 𝟭 IntegralDenseOpenRationalScheme.{u} ≅
    toNative ⋙ IntegralDominantRationalScheme.toDenseOpen :=
  NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    change f ≫ 𝟙 Y = 𝟙 X ≫
      IntegralDominantRationalScheme.denseHom (nativeHom f)
    rw [Category.comp_id]
    rw [Category.id_comp]
    exact (IntegralDominantRationalScheme.denseHom_nativeHom f).symm)

end IntegralDenseOpenRationalScheme
end AlgebraicGeometry
end
