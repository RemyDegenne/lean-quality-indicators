@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace DenseOpenRationalSchemeOver

/-- Bundle a native quotient rational map with its two required properties. -/
def hom {S : Scheme.{u}} {X Y : DenseOpenRationalSchemeOver S}
    (r : X.toScheme ⤏ Y.toScheme) (hr : r.PullsDenseOpens)
    (hS : @Scheme.RationalMap.IsOver _ _ S
      (.ofHom X.toBase) (.ofHom Y.toBase) r) : Hom X Y := ⟨r, hr, hS⟩

end DenseOpenRationalSchemeOver
end AlgebraicGeometry
end
