/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Flat.DirectSum
public import CoherentModules.RingTheory.Flat.Pi
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Faithful flatness of families of localizations

The dependent direct sum of the canonical localizations away from a family
of elements is faithfully flat if and only if the family spans the unit
ideal. Each localization is flat. When the generators span the unit ideal,
every proper ideal has a nontrivial quotient-tensor fiber in at least one
localization. The detecting localization may depend on the ideal; no individual
localization need be faithfully flat.

The analogous product criterion holds for finite families of principal
localizations. For arbitrary products of localizations at submonoids, faithful
flatness is characterized by flatness of the whole product and disjointness of
some denominator submonoid from each finitely generated proper ideal.

The ring, index type and localization carriers have independent universes.
Arbitrary index types are allowed for the direct-sum and submonoid-product
criteria; only the product unit-span criterion requires finite indices. Empty
families and subsingleton commutative rings are allowed.

## References

The proofs specialize CoherentModules' joint ideal criteria
`Module.FaithfullyFlat.directSum_iff` and `Module.FaithfullyFlat.pi_algebra_iff`.
They use Mathlib's localization flatness, disjoint-powers covering theorem
`Ideal.exists_disjoint_powers_of_span_eq_top`, localization-ideal criterion
`IsLocalization.map_algebraMap_ne_top_iff_disjoint`, and quotient-tensor
equivalence `Ideal.qoutMapEquivTensorQout`. The finite-product corollary uses
Mathlib's linear equivalence between finite direct sums and products.
-/

@[expose] public section

open scoped DirectSum TensorProduct

universe u v w

namespace Module.FaithfullyFlat

private theorem nontrivial_quot_tensor_localization_iff
    {R : Type u} [CommRing R] (I : Ideal R) (S : Submonoid R)
    (A : Type w) [CommRing A] [Algebra R A] [IsLocalization S A] :
    Nontrivial ((R ⧸ I) ⊗[R] A) ↔ Disjoint (S : Set R) (I : Set R) := by
  exact (TensorProduct.comm R (R ⧸ I) A).toEquiv.nontrivial_congr.trans <|
    (Ideal.qoutMapEquivTensorQout (R := R) (I := I) A).toEquiv.nontrivial_congr.symm.trans <|
    Ideal.Quotient.nontrivial_iff.trans <|
    IsLocalization.map_algebraMap_ne_top_iff_disjoint S A I

private theorem nontrivial_quot_tensor_away_iff
    {R : Type u} [CommRing R] (I : Ideal R) (r : R) :
    Nontrivial ((R ⧸ I) ⊗[R] Localization.Away r) ↔
      Disjoint (Submonoid.powers r : Set R) (I : Set R) :=
  nontrivial_quot_tensor_localization_iff I (Submonoid.powers r) (Localization.Away r)

/-- The dependent direct sum of the canonical principal localizations is
faithfully flat if and only if the generators span the unit ideal. Individual
localizations need not be faithfully flat: the detecting component in
`Module.FaithfullyFlat.directSum_iff` may depend on the proper ideal. The proof
uses Mathlib's disjoint-powers covering and localization-ideal criteria. -/
theorem directSum_away_iff (R : Type u) [CommRing R] {ι : Type v} (s : ι → R) :
    Module.FaithfullyFlat R (⨁ i, Localization.Away (s i)) ↔
      Ideal.span (Set.range s) = ⊤ := by
  classical
  rw [Module.FaithfullyFlat.directSum_iff R (fun i ↦ Localization.Away (s i))]
  constructor
  · rintro ⟨_, h⟩
    by_contra hspan
    obtain ⟨i, hi⟩ := h (Ideal.span (Set.range s)) hspan
    exact Set.disjoint_left.mp
      ((nontrivial_quot_tensor_away_iff _ (s i)).mp hi)
      (Submonoid.mem_powers (s i))
      (Ideal.mem_span_range_self (f := s) (x := i))
  · intro hspan
    refine ⟨fun i ↦ IsLocalization.flat (Localization.Away (s i)) (Submonoid.powers (s i)), ?_⟩
    intro I hI
    obtain ⟨r, ⟨i, rfl⟩, hdisjoint⟩ :=
      Ideal.exists_disjoint_powers_of_span_eq_top (Set.range s) hspan I hI
    exact ⟨i, (nontrivial_quot_tensor_away_iff I (s i)).mpr hdisjoint.symm⟩

/-- A product of localizations at arbitrary submonoids is faithfully flat
exactly when the whole product is flat and every finitely generated proper
ideal is disjoint from at least one denominator submonoid. This concerns the
diagonal action of the common coefficient ring, not localization of a product
ring at a single common denominator. -/
theorem pi_localization_iff
    (R : Type u) [CommRing R] {ι : Type v} (S : ι → Submonoid R)
    (A : ι → Type w) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, IsLocalization (S i) (A i)] :
    Module.FaithfullyFlat R (Π i, A i) ↔
      Module.Flat R (Π i, A i) ∧
        ∀ I : Ideal R, I.FG → I ≠ ⊤ →
          ∃ i, Disjoint (S i : Set R) (I : Set R) := by
  rw [pi_algebra_iff R A]
  refine and_congr_right fun _ ↦ forall_congr' fun I ↦
    imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ ?_
  exact exists_congr fun i ↦ nontrivial_quot_tensor_localization_iff I (S i) (A i)

/-- A finite product of canonical principal localizations is faithfully flat
if and only if the generators span the unit ideal. Empty families and
subsingleton coefficient rings are allowed. The finite-index condition is
necessary in general: coordinate idempotents in an infinite product ring can
have a faithfully flat localization product while spanning a proper ideal. -/
theorem pi_away_iff (R : Type u) [CommRing R] {ι : Type v} [Finite ι]
    (s : ι → R) :
    Module.FaithfullyFlat R (Π i, Localization.Away (s i)) ↔
      Ideal.span (Set.range s) = ⊤ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [← directSum_away_iff R s]
  let e := DirectSum.linearEquivFunOnFintype R ι (fun i ↦ Localization.Away (s i))
  constructor
  · intro h
    let := h
    exact of_linearEquiv R _ e
  · intro h
    let := h
    exact of_linearEquiv R _ e.symm

end Module.FaithfullyFlat
