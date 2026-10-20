public section

open Matrix

namespace TauCeti

universe u v

variable (l : Type*) [DecidableEq l] [Fintype l] (R : Type u) [CommRing R]

section FinIndex

variable (m : ℕ) (R : Type u)

variable [CommRing R]

namespace GLSymplecticFin

variable {m R}

@[simp]
theorem positiveLongRootTransvectionUnit_add (i : Fin m) (c d : R) :
    positiveLongRootTransvectionUnit i (c + d) =
      positiveLongRootTransvectionUnit i c * positiveLongRootTransvectionUnit i d := by
  simpa only [positiveLongRootTransvectionHom_apply, toAdd_ofAdd, toAdd_mul] using
    ((positiveLongRootTransvectionHom (R := R) i).map_mul
      (Multiplicative.ofAdd c) (Multiplicative.ofAdd d))

end GLSymplecticFin
end FinIndex
end TauCeti
end
