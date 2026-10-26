/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.SplitQuadric.Basic
public import ToricIdeals.SplitQuadric.Exponents

/-!
# The determinantal parametrization as a map of monoid algebras

`SplitQuadric.theta` is Mathlib's existing `AddMonoidAlgebra.mapDomainAlgHom`
for `ToricIdeals.SplitQuadric.exponentMap`. This identifies polynomial
substitution with the map that sums coefficients along exponent fibers.
The coefficient ring is arbitrary, including zero rings and rings with nilpotents.

## Implementation notes

The bridge uses polynomial algebra-homomorphism extensionality and the four
variable images. It makes no assertion about kernels, quotient rings or
surjectivity. No coefficient or exponent-map construction is duplicated.

## References

* Mathlib, `Algebra/MonoidAlgebra/Basic` and `Algebra/MonoidAlgebra/MapDomain`:
  the existing `AddMonoidAlgebra.mapDomainAlgHom` and its monomial computation.
* Mathlib, `Algebra/MvPolynomial/Basic`: the additive-monoid-algebra
  representation of multivariate polynomials and `MvPolynomial.algHom_ext`.
* `ToricIdeals.SplitQuadric.Exponents`: the additive determinantal exponent map and its
  coordinate computations.
-/

@[expose] public section

noncomputable section

universe u

namespace SplitQuadric

open ToricIdeals.SplitQuadric

private theorem parametrization_single (i : Fin 4) :
    exponentMap (Finsupp.single i 1) =
      ![Finsupp.single (0 : Fin 3) 1,
        Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1,
        Finsupp.single (1 : Fin 3) 1,
        Finsupp.single (1 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1] i := by
  fin_cases i <;> simp

variable (A : Type u) [CommRing A]

/-- Polynomial substitution by `(W, WT, Y, YT)` is the existing algebra
homomorphism induced by the additive determinantal exponent map. -/
theorem theta_eq_mapDomainAlgHom :
    theta A =
      AddMonoidAlgebra.mapDomainAlgHom A A exponentMap := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [theta_X]
  change parameterValues A i =
    AddMonoidAlgebra.mapDomain exponentMap
      (AddMonoidAlgebra.single (Finsupp.single i 1) (1 : A))
  rw [AddMonoidAlgebra.mapDomain_single, parametrization_single]
  fin_cases i
  · change (MvPolynomial.X (0 : Fin 3) : ParameterPolynomial A) =
      MvPolynomial.monomial (Finsupp.single (0 : Fin 3) 1) (1 : A)
    rfl
  · change (MvPolynomial.X (0 : Fin 3) : ParameterPolynomial A) * MvPolynomial.X 2 =
      MvPolynomial.monomial
        (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) (1 : A)
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one]
  · change (MvPolynomial.X (1 : Fin 3) : ParameterPolynomial A) =
      MvPolynomial.monomial (Finsupp.single (1 : Fin 3) 1) (1 : A)
    rfl
  · change (MvPolynomial.X (1 : Fin 3) : ParameterPolynomial A) * MvPolynomial.X 2 =
      MvPolynomial.monomial
        (Finsupp.single (1 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) (1 : A)
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one]

end SplitQuadric
