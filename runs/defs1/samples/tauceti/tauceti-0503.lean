public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

variable (R : Type*) [CommSemiring R]

/-- The weight of a pentagon turning on its initial side: the product of the variables that the
commuted diagram `G.swapColumns a (finRotate n a)` attaches to the `O`-markings the pentagon
carries. As for `GridDiagram.pentagonWeight`, the `O`-marking of column `c` of `G` contributes the
variable of column `Equiv.swap a (finRotate n a) c`. -/
noncomputable def initialPentagonWeight {x y : GridState n} (C : ColumnCommutationData G)
    (P : GridInitialPentagonBetween C.column C.turnRow x y) : MvPolynomial (Fin n) R :=
  ∏ c ∈ G.OColumnsOfSquares P.coveredSquares,
    MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) c)

end GridDiagram
end TauCeti
end
