/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.Teichmuller
public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Intersections of Frobenius ranges

For a reduced commutative ring of exponential characteristic `p`, the intersection
of the ranges of all iterated Frobenius maps is perfect. In prime characteristic,
its inclusion is a `PerfectionMap`, so Mathlib's `PerfectionMap.equiv` and
`PerfectionMap.lift` identify it with the perfection and give its universal property.
For a field, the intersection of the Frobenius field ranges is the largest perfect
subfield, with its field structure inherited from the stock `Subfield`.

The coefficient-image construction uses the Teichmüller image theorem at the zero
ideal and Mathlib's quotient and perfection transport. It introduces no additional
core object or compatible-root construction. Exponential characteristic one is
included in the standalone perfectness statements; the perfection-map statements
use prime characteristic, as required by Mathlib's perfection ring structure.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition, I §7, (7.1), for the residue-representative theorem whose algebraic
  perfect-core consequence is generalized here.
* Mathlib's `RingTheory/Perfection.lean` and `RingTheory/Teichmuller.lean`
  (Kenny Lau), for the perfection and its universal property.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Subring

variable {R : Type u} [CommRing R] (p : ℕ) [ExpChar R p]

/-- Membership in the intersection of Frobenius ranges means that roots of every
`p`-power depth exist, without a compatibility condition on the witnesses. -/
theorem mem_iInf_range_iterateFrobenius (x : R) :
    x ∈ (⨅ n : ℕ, (iterateFrobenius R p n).range : Subring R) ↔
      ∀ n : ℕ, ∃ y : R, y ^ (p ^ n) = x := by
  simp only [Subring.mem_iInf, RingHom.mem_range, iterateFrobenius_def]

end Subring

namespace Perfection

section CoefficientData

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    [IsReduced R]

private instance quotientBot_charP : CharP (R ⧸ (⊥ : Ideal R)) p :=
  charP_of_injective_ringHom (f := (RingEquiv.quotientBot R).symm.toRingHom)
    (RingEquiv.quotientBot R).symm.injective p

private instance quotientBot_reduced : IsReduced (R ⧸ (⊥ : Ideal R)) :=
  isReduced_of_injective (RingEquiv.quotientBot R).toRingHom
    (RingEquiv.quotientBot R).injective

omit [IsReduced R] in
private theorem map_quotientBot_bijective :
    Function.Bijective (map p (Ideal.Quotient.mk (⊥ : Ideal R))) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨map p (RingEquiv.quotientBot R).toRingHom, ?_, ?_⟩
  · intro a
    apply Perfection.ext
    intro n
    simp only [coeff_map]
    exact RingEquiv.quotientBot_mk _
  · intro a
    apply Perfection.ext
    intro n
    simp only [coeff_map]
    exact (RingEquiv.quotientBot R).symm_apply_apply _

omit [IsReduced R] in
private theorem teichmuller_map_quotientBot (a : Perfection R p) :
    teichmuller₀ p (⊥ : Ideal R) (map p (Ideal.Quotient.mk (⊥ : Ideal R)) a) = coeff R p 0 a :=
  teichmuller₀_mapMonoidHom_idealQuotientMk

private theorem coeff_zero_injective : Function.Injective (coeff R p 0) := by
  intro a b h
  apply (map_quotientBot_bijective R p).injective
  apply teichmuller₀_injective p (⊥ : Ideal R)
  simpa only [teichmuller_map_quotientBot] using h

private theorem mem_range_coeff_zero (x : R) :
    x ∈ Set.range (coeff R p 0) ↔ ∀ n : ℕ, ∃ y : R, y ^ (p ^ n) = x := by
  rw [← mem_range_teichmuller₀_iff p (⊥ : Ideal R) x]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨map p (Ideal.Quotient.mk (⊥ : Ideal R)) a, teichmuller_map_quotientBot R p a⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, rfl⟩ := (map_quotientBot_bijective R p).surjective a
    exact ⟨b, (teichmuller_map_quotientBot R p b).symm.trans ha⟩

private def coeffToFrobeniusRanges :
    Perfection R p →+* (⨅ n : ℕ, (iterateFrobenius R p n).range : Subring R) :=
  (coeff R p 0).codRestrict _ fun a ↦
    (Subring.mem_iInf_range_iterateFrobenius p _).mpr
      ((mem_range_coeff_zero R p _).mp ⟨a, rfl⟩)

private theorem coeffToFrobeniusRanges_apply (a : Perfection R p) :
    (coeffToFrobeniusRanges R p a : R) = coeff R p 0 a := rfl

private theorem coeffToFrobeniusRanges_bijective :
    Function.Bijective (coeffToFrobeniusRanges R p) := by
  constructor
  · intro a b h
    exact coeff_zero_injective R p (congrArg Subtype.val h)
  · intro x
    obtain ⟨a, ha⟩ := (mem_range_coeff_zero R p x).mpr
      ((Subring.mem_iInf_range_iterateFrobenius p (x : R)).mp x.property)
    exact ⟨a, Subtype.ext ha⟩

private def coeffFrobeniusRangesEquiv :
    Perfection R p ≃+* (⨅ n : ℕ, (iterateFrobenius R p n).range : Subring R) :=
  RingEquiv.ofBijective (coeffToFrobeniusRanges R p)
    (coeffToFrobeniusRanges_bijective R p)

end CoefficientData

end Perfection

namespace Subring

section ExponentialCharacteristic

variable {R : Type u} [CommRing R] (p : ℕ) [ExpChar R p]

/-- The intersection of all Frobenius ranges in a reduced ring is perfect.
Reducedness is needed to recover compatible roots from separately existing roots.
This generalizes the algebraic perfect-core consequence of Fesenko–Vostokov,
I §7, (7.1), to reduced rings. -/
instance (priority := 100) perfectRing_iInf_range_iterateFrobenius [IsReduced R] :
    PerfectRing (⨅ n : ℕ, (iterateFrobenius R p n).range : Subring R) p := by
  rcases expChar_is_prime_or_one R p with hp | rfl
  · let : Fact p.Prime := ⟨hp⟩
    let : CharP R p := (expChar_prime_iff R hp).mp inferInstance
    let e := Perfection.coeffFrobeniusRangesEquiv R p
    constructor
    constructor
    · intro x y h
      apply e.symm.injective
      apply (injective_frobenius (Perfection R p) p)
      simpa only [map_pow, frobenius_def] using congrArg e.symm h
    · intro x
      obtain ⟨a, ha⟩ := surjective_frobenius (Perfection R p) p (e.symm x)
      exact ⟨e a, (e.map_pow a p).symm.trans
        ((congrArg e ha).trans (e.apply_symm_apply x))⟩
  · infer_instance

/-- Every perfect subring lies in the intersection of Frobenius ranges. -/
theorem le_iInf_range_iterateFrobenius (S : Subring R) [PerfectRing S p] :
    S ≤ (⨅ n : ℕ, (iterateFrobenius R p n).range : Subring R) := by
  intro x hx
  apply (mem_iInf_range_iterateFrobenius p x).mpr
  intro n
  obtain ⟨y, hy⟩ := (powMulEquiv S (p ^ n)).surjective ⟨x, hx⟩
  exact ⟨(y : R), congrArg (fun z : S ↦ (z : R)) hy⟩

end ExponentialCharacteristic

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    [IsReduced R]

/-- The inclusion of the Frobenius-range intersection is a perfection map.
Its associated equivalence and universal lifting map are `PerfectionMap.equiv`
and `PerfectionMap.lift`; no perfectness of the ambient ring is assumed. -/
theorem perfectionMap_iInf_range_iterateFrobenius :
    PerfectionMap p
      (⨅ n : ℕ, (iterateFrobenius R p n).range : Subring R).subtype := by
  refine PerfectionMap.mk' (Perfection.coeffFrobeniusRangesEquiv R p).symm ?_
  apply Perfection.hom_ext
  intro x
  change (x : R) = ((Perfection.coeffFrobeniusRangesEquiv R p)
    ((Perfection.coeffFrobeniusRangesEquiv R p).symm x) : R)
  exact (congrArg Subtype.val
    ((Perfection.coeffFrobeniusRangesEquiv R p).apply_symm_apply x)).symm

/-- The equivalence supplied by the inclusion sends a perfection element to
its zeroth coefficient, regarded as an element of the intersection. -/
@[simp]
theorem coe_perfectionMap_iInf_range_iterateFrobenius_symm (a : Perfection R p) :
    (((perfectionMap_iInf_range_iterateFrobenius R p).equiv.symm a) : R) =
      Perfection.coeff R p 0 a :=
  (perfectionMap_iInf_range_iterateFrobenius R p).comp_symm_equiv a

end Subring

namespace Subfield

section ExponentialCharacteristic

variable {K : Type v} [Field K] (p : ℕ) [ExpChar K p]

/-- The Frobenius field-range intersection has the same underlying subring as
the Frobenius ring-range intersection. -/
theorem toSubring_iInf_fieldRange_iterateFrobenius :
    (⨅ n : ℕ, (iterateFrobenius K p n).fieldRange : Subfield K).toSubring =
      (⨅ n : ℕ, (iterateFrobenius K p n).range : Subring K) := by
  ext x
  simp only [Subfield.mem_toSubring, Subfield.mem_iInf, RingHom.mem_fieldRange,
    Subring.mem_iInf, RingHom.mem_range]

/-- Membership in the Frobenius field-range intersection is all-depth root
existence in the ambient field. -/
theorem mem_iInf_fieldRange_iterateFrobenius (x : K) :
    x ∈ (⨅ n : ℕ, (iterateFrobenius K p n).fieldRange : Subfield K) ↔
      ∀ n : ℕ, ∃ y : K, y ^ (p ^ n) = x := by
  simp only [Subfield.mem_iInf, RingHom.mem_fieldRange, iterateFrobenius_def]

/-- The intersection of Frobenius field ranges is perfect, with the field
structure of the stock subfield. This is the algebraic perfect-core consequence
of Fesenko–Vostokov, I §7, (7.1), not the full residue-representative theorem. -/
instance (priority := 100) perfectRing_iInf_fieldRange_iterateFrobenius :
    PerfectRing (⨅ n : ℕ, (iterateFrobenius K p n).fieldRange : Subfield K) p := by
  have h := Subring.perfectRing_iInf_range_iterateFrobenius (R := K) p
  rw [← toSubring_iInf_fieldRange_iterateFrobenius p] at h
  exact h

/-- Every perfect subfield lies in the Frobenius field-range intersection. -/
theorem le_iInf_fieldRange_iterateFrobenius (S : Subfield K) [PerfectRing S p] :
    S ≤ (⨅ n : ℕ, (iterateFrobenius K p n).fieldRange : Subfield K) := by
  change S.toSubring ≤
    (⨅ n : ℕ, (iterateFrobenius K p n).fieldRange : Subfield K).toSubring
  rw [toSubring_iInf_fieldRange_iterateFrobenius p]
  exact Subring.le_iInf_range_iterateFrobenius p S.toSubring

end ExponentialCharacteristic

variable (K : Type v) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The inclusion of the Frobenius field-range intersection is a perfection map,
using the stock subfield and the same reduced-ring perfection engine. -/
theorem perfectionMap_iInf_fieldRange_iterateFrobenius :
    PerfectionMap p
      (⨅ n : ℕ, (iterateFrobenius K p n).fieldRange : Subfield K).subtype := by
  -- Bind perfectness when transporting the dependent inclusion contract.
  have h : ∀ [PerfectRing (⨅ n : ℕ, (iterateFrobenius K p n).range : Subring K) p],
      PerfectionMap p (⨅ n : ℕ, (iterateFrobenius K p n).range : Subring K).subtype := by
    intro _
    exact Subring.perfectionMap_iInf_range_iterateFrobenius K p
  rw [← toSubring_iInf_fieldRange_iterateFrobenius p] at h
  exact @h (perfectRing_iInf_fieldRange_iterateFrobenius p)

/-- Zeroth coefficient is the underlying value of the inverse equivalence
supplied by the field-intersection inclusion contract. -/
@[simp]
theorem coe_perfectionMap_iInf_fieldRange_iterateFrobenius_symm (a : Perfection K p) :
    (((perfectionMap_iInf_fieldRange_iterateFrobenius K p).equiv.symm a) : K) =
      Perfection.coeff K p 0 a :=
  (perfectionMap_iInf_fieldRange_iterateFrobenius K p).comp_symm_equiv a

end Subfield
