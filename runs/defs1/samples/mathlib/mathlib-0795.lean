@[expose] public section

noncomputable section

open Polynomial Module

namespace Derivation

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M]
  [Module A M] [Module R M] (d : Derivation R A M)

set_option backward.defeqAttrib.useBackward true in
/--
The `R`-derivation from `A[X]` to `M[X]` which applies the derivative to each
of the coefficients.
-/
def mapCoeffs : Derivation R A[X] (PolynomialModule A M) where
  __ := (PolynomialModule.map A d.toLinearMap).comp
    PolynomialModule.equivPolynomial.symm.toLinearMap
  map_one_eq_zero' := by simp
  leibniz' p q := by
    dsimp
    induction p using Polynomial.induction_on' with
    | add => simp only [add_mul, map_add, add_smul, smul_add, add_add_add_comm, *]
    | monomial n a =>
      induction q using Polynomial.induction_on' with
      | add => simp only [mul_add, map_add, add_smul, smul_add, add_add_add_comm, *]
      | monomial m b => ext; simp [Polynomial.monomial_mul_monomial, add_comm]

end Derivation
end
end
