@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDominantRationalSchemeOver

/-- Bundle a native quotient and its dominance and chosen-map over-base witnesses. -/
def hom {S : Scheme.{u}} {X Y : IntegralDominantRationalSchemeOver S}
    (r : X.toScheme ⤏ Y.toScheme) (hr : r.IsDominant)
    (hS : @Scheme.RationalMap.IsOver _ _ S (.ofHom X.toBase) (.ofHom Y.toBase) r) :
    Hom X Y := ⟨r, hr, hS⟩

end IntegralDominantRationalSchemeOver
end AlgebraicGeometry
end
