public section

namespace Matrix.UnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

/-- Positions on the `r`-th superdiagonal of an `n` by `n` matrix. -/
abbrev superdiagonalIndex (n r : ℕ) : Type :=
  {ij : Fin n × Fin n // ij.2.val = ij.1.val + r}

end Matrix.UnitriangularGroup
end
