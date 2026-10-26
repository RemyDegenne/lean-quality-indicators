/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Integral closure of multivariate polynomial rings

A multivariate polynomial ring over an integrally closed domain is integrally closed,
with no finiteness assumption on the variable type.

The proof embeds the coefficient ring into its fraction field. Mathlib's coefficientwise
integrality theorem puts every integral polynomial over that field in the image of the
original polynomial ring. Integral closure then descends from the polynomial ring over
the fraction field, which is a unique factorization domain. This follows the fraction-field
and coefficientwise approach of Mathlib's univariate instance in
`Mathlib.RingTheory.Polynomial.IsIntegral`.

## References

* [Stacks Project, Tag 030A](https://stacks.math.columbia.edu/tag/030A): polynomial rings
  over normal domains.
* Mathlib's `MvPolynomial.isIntegral_iff_isIntegral_coeff` and
  `MvPolynomial.mem_range_map_iff_coeffs_subset` supply coefficient integrality and the
  characterization of the coefficient-map image.
* Mathlib's `MvPolynomial.uniqueFactorizationMonoid`,
  `UniqueFactorizationMonoid.instIsIntegrallyClosed` and
  `IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn` supply integral
  closure over the fraction field and its descent.
-/

public section

universe u v

namespace MvPolynomial

/-- A multivariate polynomial ring over an integrally closed domain is integrally closed.
The coefficient and variable types may lie in independent universes; the variable type
may be empty or infinite. See Stacks Project, Tag 030A. -/
instance isIntegrallyClosed
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {ι : Type v} : IsIntegrallyClosed (MvPolynomial ι R) := by
  let K := FractionRing R
  letI : Algebra (MvPolynomial ι R) (MvPolynomial ι K) := algebraMvPolynomial
  have : IsIntegrallyClosed (MvPolynomial ι K) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  suffices IsIntegrallyClosedIn (MvPolynomial ι R) (MvPolynomial ι K) from
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn _ (MvPolynomial ι K)
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, ?_⟩
  · simpa only [algebraMap_def] using
      (map_injective (algebraMap R K) (IsFractionRing.injective R K) :
        Function.Injective (map (algebraMap R K) : MvPolynomial ι R → MvPolynomial ι K))
  · intro p hp
    rw [algebraMap_def]
    apply mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    obtain ⟨n, _, rfl⟩ := mem_coeffs_iff.mp hc
    exact IsIntegrallyClosed.isIntegral_iff.mp ((isIntegral_iff_isIntegral_coeff.mp hp) n)

/-- Over a unique factorization domain, this instance agrees with Mathlib's
integral-closure instance for unique factorization domains. -/
private theorem isIntegrallyClosed_eq_of_uniqueFactorizationMonoid
    {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {ι : Type v} :
    @isIntegrallyClosed R _ _ (UniqueFactorizationMonoid.instIsIntegrallyClosed (A := R)) ι =
      UniqueFactorizationMonoid.instIsIntegrallyClosed (A := MvPolynomial ι R) :=
  Subsingleton.elim _ _

end MvPolynomial
