/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Reduced
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Module

@[expose] public section

set_option warningAsError true

/-!
# Reduced prime localizations and scheme stalks

The reduced prime-localization locus is the complement of the module support
of the nilradical. On a locally Noetherian scheme, reducedness of stalks is an
open condition.

## References

* R. Vakil, *The Rising Sea: Foundations of Algebraic Geometry*.
* Mathlib's localization of ideal radicals, module support and affine scheme stalks.
-/

open AlgebraicGeometry

universe u v

/-- A prime localization is reduced exactly when the nilradical of the base
ring vanishes at that prime. -/
theorem IsLocalization.AtPrime.isReduced_iff_not_mem_support_nilradical
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (S : Type v) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S p.asIdeal] :
    _root_.IsReduced S ↔ p ∉ Module.support R (nilradical R) := by
  have hnil : (nilradical R).map (algebraMap R S) = nilradical S := by
    simpa only [nilradical, Ideal.zero_eq_bot, Ideal.map_bot] using
      (IsLocalization.map_radical p.asIdeal.primeCompl S (⊥ : Ideal R))
  rw [← nilradical_eq_bot_iff, ← hnil, Ideal.map_eq_bot_iff_le_ker,
    Module.notMem_support_iff']
  constructor
  · intro h m
    obtain ⟨r, hr⟩ :=
      (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl S (m : R)).mp (h m.property)
    refine ⟨r, Ideal.mem_primeCompl_iff.mp r.property, ?_⟩
    exact Subtype.ext hr
  · intro h x hx
    obtain ⟨r, hr, hzero⟩ := h (⟨x, hx⟩ : nilradical R)
    apply (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl S x).mpr
    exact ⟨⟨r, Ideal.mem_primeCompl_iff.mpr hr⟩, congrArg Subtype.val hzero⟩

namespace PrimeSpectrum

/-- The primes where the prime localization is nonreduced form the module
support of the nilradical. -/
theorem nonreduced_atPrime_eq_support_nilradical
    {R : Type u} [CommRing R] :
    {p : PrimeSpectrum R | ¬ _root_.IsReduced (Localization.AtPrime p.asIdeal)} =
      Module.support R (nilradical R) := by
  ext p
  simpa only [Set.mem_ofPred_eq, not_not] using
    (IsLocalization.AtPrime.isReduced_iff_not_mem_support_nilradical
      p (Localization.AtPrime p.asIdeal)).not

/-- A finite nilradical module suffices for openness of the reduced
prime-localization locus. Finite generation is not necessary for openness. -/
theorem isOpen_isReduced_atPrime
    {R : Type u} [CommRing R] [Module.Finite R (nilradical R)] :
    IsOpen {p : PrimeSpectrum R |
      _root_.IsReduced (Localization.AtPrime p.asIdeal)} := by
  have hclosed : IsClosed (Module.support R (nilradical R)) := Module.isClosed_support
  convert hclosed.isOpen_compl using 1
  ext p
  exact (IsLocalization.AtPrime.isReduced_iff_not_mem_support_nilradical
    p (Localization.AtPrime p.asIdeal))

end PrimeSpectrum

namespace AlgebraicGeometry

/-- On a locally Noetherian scheme, the points with reduced local rings form
an open subset; see Vakil, *The Rising Sea: Foundations of Algebraic Geometry*. -/
theorem isOpen_setOf_isReduced_stalk
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsOpen {x : X | _root_.IsReduced (X.presheaf.stalk x)} := by
  apply (X.affineCover.isOpenCover_opensRange.isOpen_iff_coe_preimage).mpr
  intro i
  let U : X.Opens := (X.affineCover.f i).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f i)
  have hNoetherian : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hfinite : Module.Finite Γ(X, U) (nilradical Γ(X, U)) := by
    have hIdeal : _root_.IsNoetherian Γ(X, U) (nilradical Γ(X, U)) :=
      isNoetherian_submodule.mpr (fun ideal _ => hNoetherian.noetherian ideal)
    exact ⟨hIdeal.noetherian ⊤⟩
  have hopen : IsOpen {p : PrimeSpectrum Γ(X, U) |
      _root_.IsReduced (Localization.AtPrime p.asIdeal)} :=
    @PrimeSpectrum.isOpen_isReduced_atPrime Γ(X, U) _ hfinite
  have hlocal : IsOpen {x : U | _root_.IsReduced (X.presheaf.stalk (x : X))} := by
    have hset : {x : U | _root_.IsReduced (X.presheaf.stalk (x : X))} =
        hU.primeIdealOf ⁻¹' {p : PrimeSpectrum Γ(X, U) |
          _root_.IsReduced (Localization.AtPrime p.asIdeal)} := by
      ext x
      change _root_.IsReduced (X.presheaf.stalk (x : X)) ↔
        _root_.IsReduced (Localization.AtPrime (hU.primeIdealOf x).asIdeal)
      let _ : Algebra Γ(X, U) (X.presheaf.stalk (x : X)) :=
        TopCat.Presheaf.algebra_section_stalk X.presheaf x
      have _ : IsLocalization.AtPrime (X.presheaf.stalk (x : X))
          (hU.primeIdealOf x).asIdeal := hU.isLocalization_stalk x
      exact (IsLocalization.AtPrime.isReduced_iff_not_mem_support_nilradical
        (hU.primeIdealOf x) (X.presheaf.stalk (x : X))).trans
          (IsLocalization.AtPrime.isReduced_iff_not_mem_support_nilradical
            (hU.primeIdealOf x) (Localization.AtPrime (hU.primeIdealOf x).asIdeal)).symm
    rw [hset]
    exact hopen.preimage hU.isoSpec.hom.homeomorph.continuous
  exact hlocal

end AlgebraicGeometry
