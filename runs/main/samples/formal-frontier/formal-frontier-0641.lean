@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDominantRationalSchemeOver

@[simp] theorem toRationalMap_comp {S : Scheme.{u}}
    {X Y Z : IntegralDominantRationalSchemeOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRationalMap = f.toRationalMap.comp g.toRationalMap := rfl

end IntegralDominantRationalSchemeOver
end AlgebraicGeometry
end
