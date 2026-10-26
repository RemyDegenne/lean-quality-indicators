/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Normal
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.MvPolynomial.Localization
import MultivariatePolynomials.IntegrallyClosed

public section

set_option warningAsError true

/-!
# Polynomial rings over locally normal rings

This file proves that polynomial rings, and multivariate polynomial rings in
arbitrarily many variables, are locally normal over a locally normal base.

The multivariate argument follows this file's existing univariate coefficient-prime
localization strategy. For a prime `p` of `MvPolynomial ι R`, contract along
`MvPolynomial.C` to a prime `q` of `R`. Local normality makes `R_q` an integrally closed
domain; Multivariate Polynomials supplies integral closure of `MvPolynomial ι R_q`.
Mathlib's coefficient localization and prime correspondence, followed by localization
at the extended prime, identify the resulting local ring with the original polynomial
local ring at `p`. Domain and integral closure transfer along this equivalence. No
global domain or nontriviality assumption on `R` is used.

## References

* [Stacks Project, Tag 030A](https://stacks.math.columbia.edu/tag/030A), cited by
  Multivariate Polynomials for the normal-domain polynomial ingredient, not for the
  entire locally normal base and two-stage localization argument here.
* [Multivariate Polynomials, `MultivariatePolynomials.IntegrallyClosed`](https://github.com/FormalFrontier/multivariate-polynomials/blob/5a678826cc76272e625a0c54eb748d3802dfe05d/MultivariatePolynomials/IntegrallyClosed.lean):
  `MvPolynomial.isIntegrallyClosed` supplies that ingredient for arbitrary variables.
* Mathlib's `MvPolynomial.isLocalization`, `IsLocalization.isPrime_of_isPrime_disjoint`
  and `IsLocalization.under_map_of_isPrime_disjoint` supply coefficient localization
  and prime correspondence.
* Mathlib's `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`,
  `IsLocalization.algEquiv` and `isIntegrallyClosed_of_isLocalization` supply iterated
  localization, its comparison equivalence and preservation of integral closure.
-/

open scoped Polynomial

universe u v

noncomputable section

/-- A polynomial ring over a locally normal ring is locally normal. -/
instance Polynomial.isLocallyNormalRing_of_isLocallyNormalRing
    {R : Type u} [CommRing R] [IsLocallyNormalRing R] :
    IsLocallyNormalRing R[X] := by
  constructor
  · intro p
    let q := p.asIdeal.comap Polynomial.C
    let S := (Localization.AtPrime q)[X]
    let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
    let _ : Algebra R[X] S := Polynomial.algebra R (Localization.AtPrime q)
    have _ : IsLocalization pc S := Polynomial.isLocalization _ _
    let pS := p.asIdeal.map (algebraMap R[X] S)
    have disj : Disjoint (pc : Set R[X]) (p.asIdeal : Set R[X]) := by
      simpa [pc, q] using! Set.disjoint_image_left.mpr
        (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
    have _ : pS.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint pc _ _ inferInstance disj
    have _ : IsLocalization.AtPrime (Localization.AtPrime pS) p.asIdeal := by
      convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
        (Localization.AtPrime pS) pS
      exact (IsLocalization.under_map_of_isPrime_disjoint pc _ inferInstance disj).symm
    let _ : IsDomain (Localization.AtPrime q) :=
      IsLocallyNormalRing.isDomain_atPrime ⟨q, inferInstance⟩
    let _ : IsIntegrallyClosed (Localization.AtPrime q) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime ⟨q, inferInstance⟩
    let _ : IsDomain S := inferInstance
    let _ : IsIntegrallyClosed S := inferInstance
    let _ : IsDomain (Localization.AtPrime pS) :=
      IsLocalization.isDomain_of_atPrime _ pS
    exact (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime pS) (Localization.AtPrime p.asIdeal)).symm.toMulEquiv.isDomain _
  · intro p
    let q := p.asIdeal.comap Polynomial.C
    let S := (Localization.AtPrime q)[X]
    let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
    let _ : Algebra R[X] S := Polynomial.algebra R (Localization.AtPrime q)
    have _ : IsLocalization pc S := Polynomial.isLocalization _ _
    let pS := p.asIdeal.map (algebraMap R[X] S)
    have disj : Disjoint (pc : Set R[X]) (p.asIdeal : Set R[X]) := by
      simpa [pc, q] using! Set.disjoint_image_left.mpr
        (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
    have _ : pS.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint pc _ _ inferInstance disj
    have _ : IsLocalization.AtPrime (Localization.AtPrime pS) p.asIdeal := by
      convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
        (Localization.AtPrime pS) pS
      exact (IsLocalization.under_map_of_isPrime_disjoint pc _ inferInstance disj).symm
    let _ : IsDomain (Localization.AtPrime q) :=
      IsLocallyNormalRing.isDomain_atPrime ⟨q, inferInstance⟩
    let _ : IsIntegrallyClosed (Localization.AtPrime q) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime ⟨q, inferInstance⟩
    let _ : IsDomain S := inferInstance
    let _ : IsIntegrallyClosed S := inferInstance
    let _ : IsIntegrallyClosed (Localization.AtPrime pS) :=
      isIntegrallyClosed_of_isLocalization _ pS.primeCompl
        pS.primeCompl_le_nonZeroDivisors
    exact IsIntegrallyClosed.of_equiv (R := Localization.AtPrime pS)
      (IsLocalization.algEquiv p.asIdeal.primeCompl
        (Localization.AtPrime pS) (Localization.AtPrime p.asIdeal)).toRingEquiv

private theorem MvPolynomial.isDomain_and_isIntegrallyClosed_atPrime
    {R : Type u} [CommRing R] [IsLocallyNormalRing R]
    {ι : Type v} (p : PrimeSpectrum (MvPolynomial ι R)) :
    IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
  let q := p.asIdeal.comap MvPolynomial.C
  let S := MvPolynomial ι (Localization.AtPrime q)
  let pc : Submonoid (MvPolynomial ι R) :=
    Submonoid.map MvPolynomial.C.toMonoidHom q.primeCompl
  let _ : Algebra (MvPolynomial ι R) S := MvPolynomial.algebraMvPolynomial
  have _ : IsLocalization pc S := MvPolynomial.isLocalization _ _
  let pS := p.asIdeal.map (algebraMap (MvPolynomial ι R) S)
  have disj : Disjoint (pc : Set (MvPolynomial ι R))
      (p.asIdeal : Set (MvPolynomial ι R)) := by
    simpa [pc, q] using! Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have _ : pS.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint pc _ _ inferInstance disj
  -- Localizing coefficients at the contracted prime does not change the final local ring.
  have _ : IsLocalization.AtPrime (Localization.AtPrime pS) p.asIdeal := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.under_map_of_isPrime_disjoint pc _ inferInstance disj).symm
  let _ : IsDomain (Localization.AtPrime q) :=
    IsLocallyNormalRing.isDomain_atPrime ⟨q, inferInstance⟩
  let _ : IsIntegrallyClosed (Localization.AtPrime q) :=
    IsLocallyNormalRing.isIntegrallyClosed_atPrime ⟨q, inferInstance⟩
  let _ : IsDomain S := inferInstance
  let _ : IsIntegrallyClosed S :=
    MvPolynomial.isIntegrallyClosed (R := Localization.AtPrime q) (ι := ι)
  let _ : IsDomain (Localization.AtPrime pS) :=
    IsLocalization.isDomain_of_atPrime _ pS
  let _ : IsIntegrallyClosed (Localization.AtPrime pS) :=
    isIntegrallyClosed_of_isLocalization _ pS.primeCompl
      pS.primeCompl_le_nonZeroDivisors
  let e := IsLocalization.algEquiv p.asIdeal.primeCompl
    (Localization.AtPrime pS) (Localization.AtPrime p.asIdeal)
  exact ⟨e.symm.toMulEquiv.isDomain _,
    IsIntegrallyClosed.of_equiv (R := Localization.AtPrime pS) e.toRingEquiv⟩

/-- A multivariate polynomial ring in arbitrarily many variables over a locally
normal ring is locally normal.

This follows the univariate instance's coefficient-prime localization strategy using
Mathlib's localization APIs and `MvPolynomial.isIntegrallyClosed` from
`MultivariatePolynomials.IntegrallyClosed`. The latter supplies the normal-domain
polynomial ingredient cited there as Stacks Project, Tag 030A; the locally normal base
and two-stage localization argument are separate. See the module references. -/
instance MvPolynomial.isLocallyNormalRing
    {R : Type u} [CommRing R] [IsLocallyNormalRing R]
    {ι : Type v} : IsLocallyNormalRing (MvPolynomial ι R) := by
  exact ⟨fun p ↦ (MvPolynomial.isDomain_and_isIntegrallyClosed_atPrime p).1,
    fun p ↦ (MvPolynomial.isDomain_and_isIntegrallyClosed_atPrime p).2⟩

/-- A multivariate polynomial ring in finitely many variables over a locally
normal ring is locally normal. -/
@[deprecated MvPolynomial.isLocallyNormalRing (since := "2026-10-17")]
theorem MvPolynomial.isLocallyNormalRing_of_isLocallyNormalRing
    {R : Type u} [CommRing R] [IsLocallyNormalRing R]
    {ι : Type*} [Finite ι] : IsLocallyNormalRing (MvPolynomial ι R) := by
  exact MvPolynomial.isLocallyNormalRing (R := R) (ι := ι)
