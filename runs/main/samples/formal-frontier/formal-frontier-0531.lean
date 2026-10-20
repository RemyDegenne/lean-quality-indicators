@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDominantRationalSchemeOver

@[simp] theorem forget_map_toRationalMap {S : Scheme.{u}}
    {X Y : IntegralDominantRationalSchemeOver S} (f : X ⟶ Y) :
    ((forget (S := S)).map f).toRationalMap = f.toRationalMap := rfl

end IntegralDominantRationalSchemeOver
end AlgebraicGeometry
end
