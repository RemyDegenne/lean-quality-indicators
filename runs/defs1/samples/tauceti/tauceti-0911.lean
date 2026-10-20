public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "b" => finRotate n C.column

variable (R : Type*) [CommSemiring R]

/-- The weight of a commutation hexagon of either kind. -/
noncomputable def commutationHexagonWeight {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    MvPolynomial (Fin n) R :=
  P.elim (G.hexagonWeight R) (G.initialHexagonWeight R)

end GridDiagram
end TauCeti
end
