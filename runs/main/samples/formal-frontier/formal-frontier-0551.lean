public section

namespace Matrix.UnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

@[simp] theorem superdiagonalCoordinateHom_apply (r : ℕ) (hr : 1 ≤ r)
    (x : superdiagonalSubgroup n R r) (ij : superdiagonalIndex n r) :
    Multiplicative.toAdd (superdiagonalCoordinateHom n R r hr x) ij =
      (x.1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2 := by
  simp [superdiagonalCoordinateHom]

end Matrix.UnitriangularGroup
end
