public section

set_option warningAsError true

noncomputable section

namespace QuadraticAlgebra

universe u v

variable {R : Type u} [CommRing R]

open nonZeroDivisors

open scoped TensorProduct

/-- Polynomial-quotient form of the total fraction ring of a quadratic
algebra. -/
@[expose]
noncomputable def fractionRingEquivAdjoinRoot (a b : R) :
    FractionRing (QuadraticAlgebra R a b) ≃ₐ[R]
      AdjoinRoot (definingPolynomial
        (algebraMap R (FractionRing R) a) (algebraMap R (FractionRing R) b)) :=
  (fractionRingEquivBaseChange a b).trans
    ((equivAdjoinRoot
      (algebraMap R (FractionRing R) a)
      (algebraMap R (FractionRing R) b)).restrictScalars R)

end QuadraticAlgebra
end
end
