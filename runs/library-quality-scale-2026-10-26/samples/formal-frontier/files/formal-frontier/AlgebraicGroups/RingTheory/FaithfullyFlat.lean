/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

/-!
# Faithfully flat ring maps and principal-open covers

This file proves that faithful flatness can be checked after localizing a ring
map along a family of elements that spans the unit ideal. It also specializes
the criterion to the finite clopen cover defined by a complete orthogonal
family of idempotents.

It also proves descent of finite *module presentation* by descending a finite
free presentation and its kernel. This does not assert finite presentation of
the algebra itself, nor does it assume a field or a nonzero base ring.

## References

* Stacks Project, Lemma 10.39.16 (tag 00HQ), for faithful flatness as
  flatness plus surjectivity on spectra; Lemma 10.83.2 (tag 03C4), for descent
  of finite module presentation by a finite free presentation and its kernel.
* Mathlib, `Mathlib.RingTheory.RingHom.FaithfullyFlat` and
  `Mathlib.RingTheory.RingHom.Flat`, for faithful flatness and local flatness;
  `Mathlib.RingTheory.Spectrum.Prime.Topology` for principal opens.
* Mathlib, `Mathlib.RingTheory.Finiteness.Descent` for finite generation
  descent, `Mathlib.Algebra.Module.FinitePresentation` for finite free
  presentations, and `Mathlib.RingTheory.Flat.Equalizer` for `tensorKerEquiv`.
-/

universe u v

open scoped TensorProduct

namespace RingHom.FaithfullyFlat

/-- A ring map is faithfully flat if it is faithfully flat after localization
away from every member of a family that spans the unit ideal in the source.
The proof combines local flatness with the spectrum-surjectivity criterion of
Stacks Project, Lemma 10.39.16 (tag 00HQ). -/
lemma ofLocalizationSpan : RingHom.OfLocalizationSpan @RingHom.FaithfullyFlat := by
  intro R S _ _ f s hs h
  rw [iff_flat_and_comap_surjective]
  constructor
  · exact RingHom.Flat.propertyIsLocal.ofLocalizationSpan f s hs fun r ↦ (h r).flat
  · intro p
    obtain ⟨r, hr, hrp⟩ : ∃ r ∈ s, p ∈ PrimeSpectrum.basicOpen r := by
      simpa using (PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs).ge
        (TopologicalSpace.Opens.mem_top p)
    obtain ⟨p', hp'⟩ :=
      (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r).ge hrp
    obtain ⟨q', hq'⟩ := (iff_flat_and_comap_surjective.mp (h ⟨r, hr⟩)).2 p'
    refine ⟨PrimeSpectrum.comap (algebraMap S (Localization.Away (f r))) q', ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply,
      ← IsLocalization.map_comp (M := Submonoid.powers r) (S := Localization.Away r)
        (T := Submonoid.powers (f r)),
      PrimeSpectrum.comap_comp_apply]
    change PrimeSpectrum.comap (algebraMap R (Localization.Away r))
      (PrimeSpectrum.comap (Localization.awayMap f r) q') = p
    rw [hq', hp']

/-- Faithful flatness can be checked on the finite clopen decomposition cut out
by a complete orthogonal family of idempotents. -/
lemma ofCompleteOrthogonalIdempotents {ι : Type v} [Fintype ι]
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (e : ι → R) (he : CompleteOrthogonalIdempotents e)
    (h : ∀ i, (Localization.awayMap f (e i)).FaithfullyFlat) :
    f.FaithfullyFlat := by
  apply ofLocalizationSpan f (Set.range e)
  · apply (Ideal.eq_top_iff_one _).mpr
    rw [← he.complete]
    exact Ideal.sum_mem _ fun i _ ↦ Ideal.subset_span (Set.mem_range_self i)
  · rintro ⟨_, i, rfl⟩
    exact h i

/-- Variant of `RingHom.FaithfullyFlat.ofCompleteOrthogonalIdempotents` for
arbitrary models of the localizations on each idempotent piece. -/
lemma ofCompleteOrthogonalIdempotents.ofIsLocalization
    {ι : Type v} [Fintype ι] {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (e : ι → R) (he : CompleteOrthogonalIdempotents e)
    (h : ∀ i, ∃ (Rᵢ Sᵢ : Type u) (_ : CommRing Rᵢ) (_ : CommRing Sᵢ)
      (_ : Algebra R Rᵢ) (_ : Algebra S Sᵢ) (_ : IsLocalization.Away (e i) Rᵢ)
      (_ : IsLocalization.Away (f (e i)) Sᵢ) (fᵢ : Rᵢ →+* Sᵢ)
      (_ : fᵢ.comp (algebraMap R Rᵢ) = (algebraMap S Sᵢ).comp f),
        fᵢ.FaithfullyFlat) : f.FaithfullyFlat := by
  apply ofLocalizationSpan.ofIsLocalization respectsIso f (Set.range e)
  · apply (Ideal.eq_top_iff_one _).mpr
    rw [← he.complete]
    exact Ideal.sum_mem _ fun i _ ↦ Ideal.subset_span (Set.mem_range_self i)
  · rintro ⟨_, i, rfl⟩
    exact h i

end RingHom.FaithfullyFlat

/-- Finite presentation of a module descends along a faithfully flat base
change, as in Stacks Project, Lemma 10.83.2 (tag 03C4): descend finite
generation, choose a finite free surjection, then descend finite generation
of its kernel through `LinearMap.tensorKerEquiv`. -/
lemma Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
    {R : Type u} (S : Type v) {M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R S]
    [Module.FinitePresentation S (S ⊗[R] M)] :
    Module.FinitePresentation R M := by
  let _ : Module.Finite R M :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  apply Module.finitePresentation_of_free_of_surjective f hf
  rw [← Module.Finite.iff_fg]
  let _ : Module.Finite S (S ⊗[R] LinearMap.ker f) := by
    rw [Module.Finite.equiv_iff (LinearMap.tensorKerEquiv S S f)]
    rw [Module.Finite.iff_fg]
    exact Module.FinitePresentation.fg_ker
      (TensorProduct.AlgebraTensorModule.lTensor S S f)
      (LinearMap.lTensor_surjective S hf)
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
