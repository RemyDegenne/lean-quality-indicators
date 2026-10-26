/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import MinimalPrimes.RingTheory.Localization.Reduced

public section

set_option warningAsError true

/-!
# Reducedness under localization and specialization

This file proves that reducedness passes from a localization at a larger prime
to a localization at a smaller prime. Geometrically, it shows that reducedness
of scheme stalks is preserved under generalization.

## References

* `IsReduced.of_isLocalization`, in
  [Minimal Primes](https://github.com/FormalFrontier/minimal-primes/blob/d2d9212d49d32d5918fe060725b694183698e5bd/MinimalPrimes/RingTheory/Localization/Reduced.lean).
* Andrew Yang's Mathlib theorem `isReduced_localizationPreserves`, in
  [LocalProperties.Reduced](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/LocalProperties/Reduced.lean).
-/

open AlgebraicGeometry TopologicalSpace

universe u v w

/-- An arbitrary localization of a reduced commutative ring is reduced.

This specialization of `IsReduced.of_isLocalization` permits the source and
target rings to live in independent universes. Use that theorem for the
commutative-semiring form. -/
@[deprecated IsReduced.of_isLocalization (since := "2026-10-18")]
theorem IsLocalization.isReduced
    {R : Type u} [CommRing R] (M : Submonoid R) (S : Type v)
    [CommRing S] [Algebra R S] [IsLocalization M S] [IsReduced R] :
    IsReduced S := by
  exact IsReduced.of_isLocalization M S

/-- Let `S` and `T` be localizations of `R` at prime ideals `q` and `p`
respectively. If `p ≤ q` and `S` is reduced, then `T` is reduced.

Indeed, `q.primeCompl ≤ p.primeCompl`, so `T` is a further localization of
`S`. -/
theorem IsLocalization.AtPrime.isReduced_of_le
    {R : Type u} (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    [IsLocalization.AtPrime S q] [IsLocalization.AtPrime T p]
    (hpq : p ≤ q) [IsReduced S] : IsReduced T := by
  have hcompl : q.primeCompl ≤ p.primeCompl := by
    intro r hrq hrp
    exact hrq (hpq hrp)
  let _ : Algebra S T :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      S T q.primeCompl p.primeCompl hcompl
  let _ : IsScalarTower R S T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      S T q.primeCompl p.primeCompl hcompl
  let _ : IsLocalization (p.primeCompl.map (algebraMap R S)) T :=
    IsLocalization.isLocalization_of_submonoid_le
      S T q.primeCompl p.primeCompl hcompl
  exact IsReduced.of_isLocalization
    (p.primeCompl.map (algebraMap R S)) T

namespace AlgebraicGeometry

/-- Reducedness of scheme stalks is preserved under generalization: if `x`
specializes to `y` and the stalk at `y` is reduced, then the stalk at `x` is
reduced. -/
theorem isReduced_stalk_of_specializes (X : Scheme.{u}) {x y : X}
    (hxy : x ⤳ y) [_root_.IsReduced (X.presheaf.stalk y)] :
    _root_.IsReduced (X.presheaf.stalk x) := by
  let i := X.affineCover.idx y
  let f := X.affineCover.f i
  let U : X.Opens := f.opensRange
  have hyU : y ∈ U := by
    obtain ⟨y', hy'⟩ := X.affineCover.covers y
    exact ⟨y', hy'⟩
  have hxU : x ∈ U := hxy.mem_open U.isOpen hyU
  let hU : IsAffineOpen U := isAffineOpen_opensRange f
  let p := hU.primeIdealOf ⟨x, hxU⟩
  let q := hU.primeIdealOf ⟨y, hyU⟩
  have hpq : p.asIdeal ≤ q.asIdeal := by
    apply (PrimeSpectrum.le_iff_specializes p q).mpr
    have hUxy : (⟨x, hxU⟩ : U) ⤳ ⟨y, hyU⟩ :=
      (subtype_specializes_iff _ _).mpr hxy
    exact hUxy.map hU.isoSpec.hom.continuous
  let _ : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hyU⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk y) q.asIdeal :=
    hU.isLocalization_stalk ⟨y, hyU⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsLocalization.AtPrime.isReduced_of_le
    (R := Γ(X, U)) (X.presheaf.stalk y) (X.presheaf.stalk x)
    (p := p.asIdeal) (q := q.asIdeal) hpq

end AlgebraicGeometry
