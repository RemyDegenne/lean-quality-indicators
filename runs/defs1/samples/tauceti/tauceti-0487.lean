public section

open Matrix

namespace TauCeti.GLSymplecticFin

universe u v

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

/-- The standard representative of the reflection in the opposite long root `-2e_i`:
`x_{-2e_i}(1) x_{2e_i}(-1) x_{-2e_i}(1)`. -/
def negativeLongRootWeylElement (i : Fin m) : GLSymplecticFin m R :=
  negativeLongRootTransvectionUnit i 1 * positiveLongRootTransvectionUnit i (-1) *
    negativeLongRootTransvectionUnit i 1

end TauCeti.GLSymplecticFin
end
