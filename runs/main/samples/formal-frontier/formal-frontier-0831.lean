@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDenseOpenRationalSchemeOver

@[simp] theorem forget_map_toRationalMap {S : Scheme.{u}}
    {X Y : IntegralDenseOpenRationalSchemeOver S} (f : X ⟶ Y) :
    IntegralDenseOpenRationalScheme.toRationalMap ((forget (S := S)).map f) =
      toRationalMap f := rfl

end IntegralDenseOpenRationalSchemeOver
end AlgebraicGeometry
end
