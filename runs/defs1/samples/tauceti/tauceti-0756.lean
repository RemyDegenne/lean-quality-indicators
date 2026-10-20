public section

open _root_.QuadraticMap

namespace QuadraticMap

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The set of represented units of a scalar-valued quadratic map.

This is the classical value set `D(Q)` over a field; over a general commutative semiring it is
the set of units represented by `Q`, rather than the full value set. -/
def unitValueSet (Q : QuadraticMap R M R) : Set Rˣ :=
  {a | Represents Q (a : R)}

end QuadraticMap
end
