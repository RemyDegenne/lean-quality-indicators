@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace DenseOpenRationalSchemeOver

theorem isOver_hom {S : Scheme.{u}} {X Y : DenseOpenRationalSchemeOver S}
    (r : X.toScheme ⤏ Y.toScheme) (hr : r.PullsDenseOpens)
    (hS : @Scheme.RationalMap.IsOver _ _ S
      (.ofHom X.toBase) (.ofHom Y.toBase) r) :
    (hom r hr hS).isOver = hS := rfl

end DenseOpenRationalSchemeOver
end AlgebraicGeometry
end
