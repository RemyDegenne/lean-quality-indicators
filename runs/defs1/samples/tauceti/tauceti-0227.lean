public section

namespace TauCeti

namespace GridInitialPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Recover the initial-side pentagon from the first rectangle and its turn-point constraints. -/
def pentagon (D : GridInitialPentagonRectangleDecomposition a s x z) :
    GridInitialPentagonBetween a s x D.middle where
  toGridRectangleBetween := D.first
  left_eq := D.first_left_eq
  turn_mem := D.first_turn_mem

end GridInitialPentagonRectangleDecomposition
end TauCeti
end
