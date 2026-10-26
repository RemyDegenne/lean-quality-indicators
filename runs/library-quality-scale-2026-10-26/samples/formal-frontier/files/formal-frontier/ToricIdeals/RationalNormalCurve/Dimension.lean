/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.KrullDimension.Polynomial
import MinimalPrimes.RingTheory.KrullDimension.Integral
public import ToricIdeals.RationalNormalCurve
import ToricIdeals.RationalNormalCurve.EndpointMap

/-!
# Krull dimensions of Hankel quotients

For Noetherian coefficients the full quotient has Krull dimension
`ringKrullDim R + (if n = 0 then 1 else 2)`. In positive degree the endpoint
map is injective and integral, reducing the dimension calculation to a
two-variable polynomial ring. At degree zero the quotient instead retains
one polynomial variable. The dimension equality includes bottom for zero
rings and infinity.

Over a Noetherian commutative coefficient ring `R`, the full Hankel quotients
in degrees zero and one have Krull dimensions `ringKrullDim R + 1` and
`ringKrullDim R + 2`, respectively. In these degrees there are no Hankel
minors, so the quotients are polynomial rings in one and two variables.
In particular, the degree-zero quotient retains its sole variable; it is
not the image of the monomial parametrization.

The dimensions take values in `WithBot ℕ∞`. No nontriviality or finite-dimension
hypothesis is imposed on `R`, so the formulas also include zero rings and
coefficient rings of infinite Krull dimension.

## References

* `ToricIdeals.RationalNormalCurve` for the vanishing Hankel ideals.
* `Mathlib.RingTheory.KrullDimension.Polynomial` for the dimension formula
  for finite-variable polynomial rings over Noetherian coefficient rings.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.EndpointMap`, for
  the injective integral endpoint map in positive degree.
* Formal Frontier Agents, `MinimalPrimes.RingTheory.KrullDimension.Integral`,
  for invariance of Krull dimension under injective integral homomorphisms.
-/

namespace ToricIdeals.RationalNormalCurve

@[expose] public section

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The full degree-zero Hankel quotient has one polynomial variable over `R`. -/
theorem ringKrullDim_quotient_hankelIdeal_zero :
    ringKrullDim (Source R 0 ⧸ hankelIdeal R 0) = ringKrullDim R + 1 := by
  rw [hankelIdeal_zero, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (Source R 0))]
  simp [Source]

/-- The full degree-one Hankel quotient has two polynomial variables over `R`. -/
theorem ringKrullDim_quotient_hankelIdeal_one :
    ringKrullDim (Source R 1 ⧸ hankelIdeal R 1) = ringKrullDim R + 2 := by
  rw [hankelIdeal_one, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (Source R 1))]
  simp [Source]

end

/-- Over a Noetherian commutative ring, the full Hankel quotient has dimension
one more than its coefficient ring in degree zero, and two more in positive
degree. The equality is in `WithBot ℕ∞`, including zero rings and infinite
dimension. The degree-zero quotient retains its polynomial variable; it is
not the raw parametrization image. -/
theorem ringKrullDim_quotient_hankelIdeal (R : Type u) [CommRing R]
    [IsNoetherianRing R] (n : ℕ) :
    ringKrullDim (Source R n ⧸ hankelIdeal R n) =
      ringKrullDim R + (if n = 0 then 1 else 2) := by
  by_cases hn : n = 0
  · subst n
    simpa using (ringKrullDim_quotient_hankelIdeal_zero (R := R))
  · rw [if_neg hn]
    calc
      ringKrullDim (Source R n ⧸ hankelIdeal R n) =
          ringKrullDim (MvPolynomial (Fin 2) R) :=
        ((endpointMap_isIntegral (R := R) n).ringKrullDim_eq
          (endpointMap_injective (R := R) n (Nat.one_le_iff_ne_zero.mpr hn))).symm
      _ = ringKrullDim R + 2 := by
        simpa using (MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite
          (R := R) (ι := Fin 2))

end

end ToricIdeals.RationalNormalCurve
