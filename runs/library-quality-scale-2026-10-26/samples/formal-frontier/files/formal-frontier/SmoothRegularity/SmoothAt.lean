/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import SmoothRegularity.StandardSmooth

/-!
# Regularity from smoothness at a prime

This file proves that a finite-type algebra over a field which is smooth at a
prime has a regular local ring at that prime.
-/

public section

namespace Algebra

universe u v

/-- If a finite-type algebra over a field is smooth at a prime, then its
localization at that prime is a regular local ring. -/
theorem IsSmoothAt.isRegularLocalRing
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
    [Algebra.FiniteType K S] (q : Ideal S) [q.IsPrime]
    (hq : Algebra.IsSmoothAt K q) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let _ : Algebra.IsSmoothAt K q := hq
  let _ : Algebra.FinitePresentation K S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K q
  let Sf := Localization.Away f
  let qf : Ideal Sf := q.map (algebraMap S Sf)
  have hdisj : Disjoint ((Submonoid.powers f : Submonoid S) : Set S) q := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  let _ : qf.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) Sf q inferInstance hdisj
  let _ : Algebra.IsStandardSmooth K Sf := hstd
  have hreg : IsRegularLocalRing (Localization.AtPrime qf) :=
    Algebra.IsStandardSmooth.isRegularLocalRing_atPrime (K := K) (S := Sf) qf
  have hcomap : qf.comap (algebraMap S Sf) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) Sf
      (I := q) inferInstance hdisj
  have e : Localization.AtPrime q ≃+* Localization.AtPrime qf := by
    exact (Localization.localRingEquiv q (qf.comap (algebraMap S Sf))
      (RingEquiv.refl S) (by
        change q = qf.comap (algebraMap S Sf)
        exact hcomap.symm)).trans
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          (Submonoid.powers f) qf).toRingEquiv
  exact IsRegularLocalRing.of_ringEquiv e.symm

end Algebra
