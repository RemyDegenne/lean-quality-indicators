/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Defs
import MultivariatePolynomials.Artinian
public import ToricIdeals.RationalNormalCurve
import ToricIdeals.RationalNormalCurve.AxisProjection

/-!
# Artinian rational-normal-curve coordinate rings

The quotient of `Source R n` by `hankelIdeal R n` is Artinian exactly when
its commutative coefficient ring `R` is a zero ring, expressed by
`Subsingleton R`. The ring criterion takes scalars in the quotient ring
itself. For the canonical coefficient `R`-module action, Artinianity has the
same zero-ring condition. Both criteria concern every degree and include
zero coefficient rings, rings with nilpotent elements and product rings.

At degree zero the Hankel ideal is `⊥`, so the quotient is the full
one-variable polynomial ring, not the parametrization kernel quotient or
image. At degree one the ideal is again `⊥`, giving the full two-variable
polynomial ring.

Sending `x₀` to `Polynomial.X` and every other variable to zero gives a
surjection from the quotient onto `Polynomial R`. Over a nonzero coefficient
ring, Artinianity would make the regular element `X` a unit, contradicting
its noninvertibility.

## References

* Mathlib contributors, `Mathlib.RingTheory.Artinian.Module`, for
  coefficient-module descent along surjective linear maps.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, for the Hankel
  presentation and its small-degree boundary results.
* Mathlib contributors, `Mathlib.RingTheory.Artinian.Defs` and
  `Mathlib.RingTheory.Artinian.Module`, for Artinianity over the ring itself,
  its descent along surjective ring homomorphisms and the regular-unit criterion.
* Mathlib contributors, `Mathlib.Algebra.MvPolynomial.Eval`,
  `Mathlib.Algebra.Polynomial.Eval.Defs`, `Mathlib.Algebra.Polynomial.Monomial`
  and `Mathlib.RingTheory.Ideal.Quotient.Defs`, for polynomial evaluation,
  homomorphism extensionality and quotient lifts.
* Mathlib contributors, `Mathlib.Algebra.Polynomial.Coeff` and
  `Mathlib.Algebra.Polynomial.Degree.Operations`, for regularity and
  noninvertibility of the polynomial variable.
* Formal Frontier Agents, `MultivariatePolynomials.Artinian`, for the
  coefficient-module criterion for univariate polynomials.
-/

@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

/-- In every degree, the quotient by the Hankel minors is Artinian as a module
over itself exactly when its commutative coefficient ring is a zero ring.
This includes degree zero and needs no nontriviality, domain or
positive-degree assumption. The proof uses Mathlib's surjective descent of
Artinianity and its criterion that regular elements of an Artinian ring are units. -/
theorem quotient_isArtinianRing_iff (R : Type u) [CommRing R] (n : ℕ) :
    IsArtinianRing (Source R n ⧸ hankelIdeal R n) ↔ Subsingleton R := by
  classical
  constructor
  · intro hArt
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact hR
    · let : Nontrivial R := hR
      have hqSurj : Function.Surjective (axisProjection R n).toRingHom :=
        axisProjection_surjective R n
      let : IsArtinianRing (Source R n ⧸ hankelIdeal R n) := hArt
      let : IsArtinianRing (Polynomial R) := hqSurj.isArtinianRing
      exact (Polynomial.not_isUnit_X (R := R)
        (IsArtinianRing.isUnit_iff_isRegular.mpr Polynomial.isRegular_X)).elim
  · intro hR
    let : Subsingleton R := hR
    have h01 : (0 : Source R n) = 1 := Subsingleton.elim _ _
    apply Ring.isArtinian_of_zero_eq_one
    simpa only [map_zero, map_one] using
      congrArg (Ideal.Quotient.mk (hankelIdeal R n)) h01

/-- In every degree, the full Hankel quotient is Artinian as a module over
its coefficient ring `R` exactly when `R` is a zero ring. The scalar action is
the canonical coefficient action, not multiplication as a quotient self-module;
no nontriviality or positive-degree assumption is needed. -/
theorem quotient_isArtinian_iff (R : Type u) [CommRing R] (n : ℕ) :
    IsArtinian R (Source R n ⧸ hankelIdeal R n) ↔ Subsingleton R := by
  constructor
  · intro hArt
    let : IsArtinian R (Source R n ⧸ hankelIdeal R n) := hArt
    have hPoly : IsArtinian R (Polynomial R) :=
      isArtinian_of_surjective (Source R n ⧸ hankelIdeal R n)
        (axisProjection R n).toLinearMap (axisProjection_surjective R n)
    exact (Polynomial.isArtinian_iff R).mp hPoly
  · intro hR
    let : Subsingleton R := hR
    let : Subsingleton (Source R n ⧸ hankelIdeal R n) :=
      Algebra.subsingleton R (Source R n ⧸ hankelIdeal R n)
    exact isArtinian_of_finite (R := R) (M := Source R n ⧸ hankelIdeal R n)

end ToricIdeals.RationalNormalCurve
