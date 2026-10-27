@[expose] public section

open Polynomial

namespace FrobeniusTwistedLine

open scoped TensorProduct

noncomputable section

variable (K : Type*) [Field K]

variable {K}

variable (K)

/-- Antipode corresponding to coordinatewise negation. -/
def antipode {p : ℕ} [Fact p.Prime] [CharP K p] (t : K) :
    CoordinateRing K p t →ₐ[K] CoordinateRing K p t :=
  lift K p t (-x K p t) (-y K p t) (coordinate_satisfiesEquation K p t).neg

end
end FrobeniusTwistedLine
end
