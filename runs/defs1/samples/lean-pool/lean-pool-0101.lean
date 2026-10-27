@[expose] public section

open scoped BigOperators

namespace BooleanIsoperimetry

/-- The non-strict simplicial order: first by weight, then by reverse binary order. -/
def simplicialLe {n : ℕ} (x y : Cube n) : Prop :=
  x.card < y.card ∨ (x.card = y.card ∧ cubeToNat y ≤ cubeToNat x)

end BooleanIsoperimetry
end
