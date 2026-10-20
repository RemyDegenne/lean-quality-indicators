public section

open CategoryTheory

namespace TauCeti.Symplectic

universe u

variable (R : Type u) [CommRing R]

@[simp]
theorem splitMaximalTorus_definingIdeal (m : ℕ) :
    (splitMaximalTorus R m).definingIdeal = diagonalTorusDefiningIdeal R m := by
  ext x
  rw [SplitMaximalTorus.mem_definingIdeal, splitMaximalTorus_coordinateMap,
    mem_diagonalTorusDefiningIdeal]

end TauCeti.Symplectic
end
