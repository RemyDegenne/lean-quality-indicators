/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Normal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

@[expose] public section

/-!
# Products of locally normal rings

Finite products of locally normal rings are locally normal, and local normality
of an arbitrary product descends to each factor. Together, these results
characterize local normality of finite products.
-/

universe u v

noncomputable section

/-- A finite product of locally normal rings is locally normal. -/
theorem IsLocallyNormalRing.pi
    {I : Type*} (S : I → Type*) [∀ i, CommRing (S i)] [Finite I]
    [∀ i, IsLocallyNormalRing (S i)] : IsLocallyNormalRing (∀ i, S i) := by
  constructor
  · intro p
    obtain ⟨i, q, hp⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
    subst p
    let e : Localization.AtPrime (q.asIdeal.comap (Pi.evalRingHom S i)) ≃+*
        Localization.AtPrime q.asIdeal :=
      RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
        (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
    let _ : IsDomain (Localization.AtPrime q.asIdeal) :=
      IsLocallyNormalRing.isDomain_atPrime q
    exact e.toMulEquiv.isDomain _
  · intro p
    obtain ⟨i, q, hp⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
    subst p
    let e : Localization.AtPrime (q.asIdeal.comap (Pi.evalRingHom S i)) ≃+*
        Localization.AtPrime q.asIdeal :=
      RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
        (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
    let _ : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime q
    exact IsIntegrallyClosed.of_equiv e.symm

/-- Each factor of a locally normal product is locally normal, without any
finiteness assumption on the index type. -/
theorem IsLocallyNormalRing.of_pi
    {I : Type u} (S : I → Type v) [∀ i, CommRing (S i)]
    [IsLocallyNormalRing (∀ i, S i)] (i : I) : IsLocallyNormalRing (S i) := by
  constructor
  · intro q
    let e : Localization.AtPrime (q.asIdeal.comap (Pi.evalRingHom S i)) ≃+*
        Localization.AtPrime q.asIdeal :=
      RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
        (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
    let _ : IsDomain (Localization.AtPrime (q.asIdeal.comap (Pi.evalRingHom S i))) :=
      IsLocallyNormalRing.isDomain_atPrime
        ⟨q.asIdeal.comap (Pi.evalRingHom S i), inferInstance⟩
    exact e.symm.toMulEquiv.isDomain _
  · intro q
    let e : Localization.AtPrime (q.asIdeal.comap (Pi.evalRingHom S i)) ≃+*
        Localization.AtPrime q.asIdeal :=
      RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
        (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
    let _ : IsIntegrallyClosed
        (Localization.AtPrime (q.asIdeal.comap (Pi.evalRingHom S i))) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime
        ⟨q.asIdeal.comap (Pi.evalRingHom S i), inferInstance⟩
    exact IsIntegrallyClosed.of_equiv e

/-- A finite product is locally normal if and only if each factor is locally
normal. -/
theorem IsLocallyNormalRing.pi_iff
    {I : Type u} (S : I → Type v) [∀ i, CommRing (S i)] [Finite I] :
    IsLocallyNormalRing (∀ i, S i) ↔ ∀ i, IsLocallyNormalRing (S i) := by
  constructor
  · intro h i
    let _ : IsLocallyNormalRing (∀ i, S i) := h
    exact IsLocallyNormalRing.of_pi S i
  · intro h
    let _ (i : I) : IsLocallyNormalRing (S i) := h i
    exact IsLocallyNormalRing.pi S
