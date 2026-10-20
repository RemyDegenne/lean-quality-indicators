public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ}

/-- Two grid diagrams differ by one elementary row commutation.

The rows are consecutive in the cyclic order on `Fin n`, have non-interleaving marking
segments in the source diagram, and are swapped to obtain the target diagram. -/
def IsRowCommutation (G G' : GridDiagram n) : Prop :=
  ∃ a : Fin n, a ≠ finRotate n a ∧
    RowsNoninterleaving G a (finRotate n a) ∧
      G' = G.swapRows a (finRotate n a)

end GridDiagram
end TauCeti
end
