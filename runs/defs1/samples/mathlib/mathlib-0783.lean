@[expose] public section

universe u v w

noncomputable section

variable (R : Type u) {B : Type v} [CommRing R]

variable (CM : Matrix B B ℤ)

variable [DecidableEq B]

namespace LieAlgebra

/-- The exceptional split Lie algebra of type e₇. -/
abbrev e₇ := Matrix.ToLieAlgebra R (CartanMatrix.E 7)

end LieAlgebra
end
end
