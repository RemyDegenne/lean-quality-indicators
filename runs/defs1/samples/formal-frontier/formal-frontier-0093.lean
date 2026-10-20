public section

set_option warningAsError true

noncomputable section

open Polynomial

namespace QuadraticAlgebra

universe u

variable {R : Type u} [CommRing R]

/-- The monic polynomial defining `QuadraticAlgebra R a b`. -/
@[expose]
def definingPolynomial (a b : R) : R[X] :=
  X ^ 2 - (C b * X + C a)

end QuadraticAlgebra
end
end
