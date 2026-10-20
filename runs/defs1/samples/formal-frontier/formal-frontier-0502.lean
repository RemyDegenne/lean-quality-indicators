@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDominantRationalScheme

/-- Package a dominant native quotient rational map as an arrow. -/
def hom {X Y : IntegralDominantRationalScheme.{u}} (r : X.toScheme ⤏ Y.toScheme)
    (hr : r.IsDominant) : Hom X Y := ⟨r, hr⟩

end IntegralDominantRationalScheme
end AlgebraicGeometry
end
