@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing DiagonalCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The terminality statement specialized to the finite empty index type. -/
def diagonalGroupSchemeFin0IsTerminal (K : Type) [CommRing K] :
    Limits.IsTerminal (diagonalGroupScheme K (Fin 0)) :=
  (Limits.isLimitEquivIsTerminalOfIsEmpty (Grp (Over (Spec (.of K))))
    (diagonalGroupProductFan K (Fin 0)))
    (diagonalGroupProductFan_isLimit K (Fin 0))

end AlgebraicGeometry
end
end
