/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Polynomial.Basic
public import ToricIdeals.RationalNormalCurve.AxisProjection

/-!
# Finite coefficient modules of Hankel quotients

In every degree, the full Hankel quotient is a finite module over its
commutative coefficient ring `R` exactly when `R` is a zero ring, expressed
by `Subsingleton R`. The scalar action is the canonical coefficient action.
This differs from finiteness over the polynomial algebra of endpoint
coordinates and from finiteness of the quotient as a module over itself.

The coefficient-linear axis projection is surjective onto `Polynomial R`.
For nontrivial coefficients, Mathlib's polynomial obstruction therefore rules
out finite generation of the quotient. For zero coefficients, the quotient
is a subsingleton module and hence finite. No Noetherian assumption is needed.
At degree zero, the Hankel ideal is bottom and the quotient is the full
one-variable polynomial ring, not the parametrization image.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.AxisProjection`,
  for the coefficient-preserving surjection in every degree.
* Mathlib contributors, `Mathlib.RingTheory.Polynomial.Basic`, for
  `Polynomial.not_finite` over every nontrivial semiring.
* Mathlib contributors, `Mathlib.RingTheory.Finiteness.Basic` and
  `Mathlib.Algebra.Module.Defs`, for surjective-image finiteness and
  finiteness of modules over subsingleton coefficients.
-/

@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

/-- In every degree, the full Hankel quotient is finite as a module over its
commutative coefficient ring exactly when that ring is a zero ring. Scalars
act canonically through coefficients, not through endpoint polynomials or
quotient self-multiplication. This includes degree zero and requires no
Noetherian, domain, nontriviality or positive-degree assumption. -/
theorem quotient_moduleFinite_iff (R : Type u) [CommRing R] (n : ℕ) :
    Module.Finite R (Source R n ⧸ hankelIdeal R n) ↔ Subsingleton R := by
  constructor
  · intro hQ
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact hR
    · let : Nontrivial R := hR
      let : Module.Finite R (Source R n ⧸ hankelIdeal R n) := hQ
      have hP : Module.Finite R (Polynomial R) :=
        Module.Finite.of_surjective (axisProjection R n).toLinearMap
          (axisProjection_surjective R n)
      exact (Polynomial.not_finite hP).elim
  · intro hR
    let : Subsingleton R := hR
    let : Subsingleton (Source R n ⧸ hankelIdeal R n) :=
      Module.subsingleton R (Source R n ⧸ hankelIdeal R n)
    let : Finite (Source R n ⧸ hankelIdeal R n) := inferInstance
    exact Module.Finite.of_finite

end ToricIdeals.RationalNormalCurve
