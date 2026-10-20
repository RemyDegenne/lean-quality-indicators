@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDominantRationalScheme

@[simp] theorem nativeHom_denseHom {X Y : IntegralDominantRationalScheme.{u}}
    (f : X ⟶ Y) : IntegralDenseOpenRationalScheme.nativeHom (denseHom f) = f := by
  apply hom_ext
  rfl

end IntegralDominantRationalScheme
end AlgebraicGeometry
end
