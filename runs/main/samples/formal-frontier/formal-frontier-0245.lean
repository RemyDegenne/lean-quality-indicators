public section

set_option warningAsError true

noncomputable section

open Polynomial

namespace QuadraticAlgebra

universe u

variable {R : Type u} [CommRing R]

theorem definingPolynomial_monic (a b : R) :
    (definingPolynomial a b).Monic := by
  exact monic_X_pow_sub degree_linear_lt

end QuadraticAlgebra
end
end
