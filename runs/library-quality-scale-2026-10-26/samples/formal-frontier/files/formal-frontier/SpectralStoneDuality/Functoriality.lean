/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.PrimeSpectrum
public import Mathlib.Topology.Spectral.Hom

/-!
# Contravariant functoriality and compact opens

A bounded lattice homomorphism `A → B` pulls prime ideals back to give the
spectral map `Spec B → Spec A`. The identity, composition and basic-open
preimage laws make this action usable without unfolding the ideal construction.
`compactOpenOrderIso` identifies `A` with the compact opens of its spectrum,
sending `a` to the open of primes not containing `a`.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.2(b), Theorem 2.2.8(1)–(2).
- Mathlib, `Order.PrimeIdeal`, `Topology.Spectral.Hom` and its bounded-lattice
  homomorphism API; Formal Frontier Agents, *Ideal Completion*, for principal ideals.
-/

public section

set_option warningAsError true

open Order Set TopologicalSpace Topology

universe u v w

namespace SpectralStoneDuality

variable {A : Type u} [DistribLattice A] [BoundedOrder A]

namespace PrimeIdealSpectrum

private def comapIdeal {B : Type v} [DistribLattice B] [BoundedOrder B]
    (f : BoundedLatticeHom A B) (P : Order.Ideal B) : Order.Ideal A where
  carrier := {a | f a ∈ P}
  nonempty' := ⟨⊥, by change f ⊥ ∈ P; rw [map_bot]; exact P.bot_mem⟩
  directed' := by
    intro a ha b hb
    refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
    change f (a ⊔ b) ∈ P
    rw [map_sup]
    exact Order.Ideal.sup_mem ha hb
  lower' := by
    intro a b hba ha
    exact P.lower (OrderHomClass.mono f hba) ha

private theorem comapIdeal_isPrime {B : Type v} [DistribLattice B] [BoundedOrder B]
    (f : BoundedLatticeHom A B) (P : Order.Ideal B) (hP : P.IsPrime) :
    (comapIdeal f P).IsPrime := by
  let _ : (comapIdeal f P).IsProper := Order.Ideal.isProper_of_notMem (by
    change f ⊤ ∉ P
    rw [map_top]
    exact hP.top_notMem)
  apply Order.Ideal.IsPrime.of_mem_or_mem
  intro a b hab
  change f (a ⊓ b) ∈ P at hab
  rw [map_inf] at hab
  exact hP.mem_or_mem hab

/-- The contravariant action of a bounded lattice homomorphism on prime spectra. -/
@[expose]
def spectrumComap {B : Type v} [DistribLattice B] [BoundedOrder B]
    (f : BoundedLatticeHom A B) : PrimeIdealSpectrum B → PrimeIdealSpectrum A :=
  fun P ↦
    let ideal : Order.Ideal A := {
      carrier := {a | f a ∈ P.1}
      nonempty' := ⟨⊥, by change f ⊥ ∈ P.1; rw [map_bot]; exact P.1.bot_mem⟩
      directed' := by
        intro a ha b hb
        refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
        change f (a ⊔ b) ∈ P.1
        rw [map_sup]
        exact Order.Ideal.sup_mem ha hb
      lower' := by
        intro a b hba ha
        exact P.1.lower (OrderHomClass.mono f hba) ha }
    have prime : ideal.IsPrime := by
      let _ : ideal.IsProper := Order.Ideal.isProper_of_notMem (by
        change f ⊤ ∉ P.1
        rw [map_top]
        exact P.2.top_notMem)
      apply Order.Ideal.IsPrime.of_mem_or_mem
      intro a b hab
      change f (a ⊓ b) ∈ P.1 at hab
      rw [map_inf] at hab
      exact P.2.mem_or_mem hab
    ⟨ideal, prime⟩

private theorem spectrumComap_eq_privateConstruction
    {B : Type v} [DistribLattice B] [BoundedOrder B]
    (f : BoundedLatticeHom A B) :
    spectrumComap f = fun P ↦
      (⟨comapIdeal f P.1, comapIdeal_isPrime f P.1 P.2⟩ : PrimeIdealSpectrum A) :=
  rfl

theorem spectrumComap_preimage_basicOpen_principal
    {B : Type v} [DistribLattice B] [BoundedOrder B]
    (f : BoundedLatticeHom A B) (a : A) :
    spectrumComap f ⁻¹' basicOpen (Order.Ideal.principal a) =
      basicOpen (Order.Ideal.principal (f a)) := by
  ext P
  simp only [Set.mem_preimage, basicOpen, Set.mem_ofPred_eq,
    Order.Ideal.principal_le_iff]
  rfl

theorem continuous_spectrumComap
    {B : Type v} [DistribLattice B] [BoundedOrder B]
    (f : BoundedLatticeHom A B) : Continuous (spectrumComap f) := by
  rw [isTopologicalBasis_basicOpen_principal.continuous_iff]
  rintro _ ⟨a, rfl⟩
  rw [spectrumComap_preimage_basicOpen_principal]
  exact isOpen_basicOpen _

theorem isSpectralMap_spectrumComap
    {B : Type v} [DistribLattice B] [BoundedOrder B]
    (f : BoundedLatticeHom A B) : IsSpectralMap (spectrumComap f) where
  toContinuous := continuous_spectrumComap f
  isCompact_preimage_of_isOpen := by
    intro s hsOpen hsCompact
    obtain ⟨I, hIs⟩ := isOpen_iff_exists_basicOpen s |>.mp hsOpen
    have hICompact : IsCompact (basicOpen I) := by
      rw [hIs]
      exact hsCompact
    obtain ⟨a, rfl⟩ := isCompact_basicOpen_iff I |>.mp hICompact
    rw [← hIs, spectrumComap_preimage_basicOpen_principal]
    exact isCompact_basicOpen_iff _ |>.mpr ⟨f a, rfl⟩

/-- The compact open `D(a)` corresponding to a lattice element `a`. -/
@[expose]
def principalCompactOpen (a : A) :
    TopologicalSpace.CompactOpens (PrimeIdealSpectrum A) :=
  ⟨⟨basicOpen (Order.Ideal.principal a),
      isCompact_basicOpen_iff _ |>.mpr ⟨a, rfl⟩⟩,
    isOpen_basicOpen _⟩

private def principalCompactOpenEmbedding :
    A ↪o TopologicalSpace.CompactOpens (PrimeIdealSpectrum A) :=
  OrderEmbedding.ofMapLEIff principalCompactOpen fun a b ↦ by
    change basicOpen (Order.Ideal.principal a) ⊆
      basicOpen (Order.Ideal.principal b) ↔ a ≤ b
    rw [basicOpen_subset_iff, Order.Ideal.principal_le_iff,
      Order.Ideal.mem_principal]

private theorem principalCompactOpen_surjective :
    Function.Surjective (principalCompactOpen (A := A)) := by
  intro U
  obtain ⟨I, hIU⟩ := isOpen_iff_exists_basicOpen
    (U : Set (PrimeIdealSpectrum A)) |>.mp U.isOpen
  have hICompact : IsCompact (basicOpen I) := by
    rw [hIU]
    exact U.isCompact
  obtain ⟨a, rfl⟩ := isCompact_basicOpen_iff I |>.mp hICompact
  refine ⟨a, ?_⟩
  apply TopologicalSpace.CompactOpens.ext
  exact hIU

/-- The order isomorphism `A ≃ QCOuv(Spec A)` from Fujiwara--Kato,
*Foundations of Rigid Geometry I*, Theorem 2.2.8(1). -/
@[expose]
noncomputable def compactOpenOrderIso :
    A ≃o TopologicalSpace.CompactOpens (PrimeIdealSpectrum A) :=
  let embedding : A ↪o TopologicalSpace.CompactOpens (PrimeIdealSpectrum A) :=
    OrderEmbedding.ofMapLEIff principalCompactOpen fun a b ↦ by
      change basicOpen (Order.Ideal.principal a) ⊆
        basicOpen (Order.Ideal.principal b) ↔ a ≤ b
      rw [basicOpen_subset_iff, Order.Ideal.principal_le_iff,
        Order.Ideal.mem_principal]
  let surjective : Function.Surjective (principalCompactOpen (A := A)) := by
    intro U
    obtain ⟨I, hIU⟩ := isOpen_iff_exists_basicOpen
      (U : Set (PrimeIdealSpectrum A)) |>.mp U.isOpen
    have hICompact : IsCompact (basicOpen I) := by
      rw [hIU]
      exact U.isCompact
    obtain ⟨a, rfl⟩ := isCompact_basicOpen_iff I |>.mp hICompact
    refine ⟨a, ?_⟩
    apply TopologicalSpace.CompactOpens.ext
    exact hIU
  OrderIso.ofSurjective embedding surjective

private theorem compactOpenOrderIso_eq_privateConstruction :
    compactOpenOrderIso (A := A) =
      OrderIso.ofSurjective principalCompactOpenEmbedding principalCompactOpen_surjective :=
  rfl

@[simp]
theorem compactOpenOrderIso_apply (a : A) :
    compactOpenOrderIso (A := A) a = principalCompactOpen a := rfl

theorem spectrumComap_id :
    spectrumComap (BoundedLatticeHom.id A) = id := by
  funext P
  apply Subtype.ext
  apply Order.Ideal.ext
  ext a
  rfl

theorem spectrumComap_comp
    {B : Type v} {C : Type w}
    [DistribLattice B] [BoundedOrder B] [DistribLattice C] [BoundedOrder C]
    (f : BoundedLatticeHom A B) (g : BoundedLatticeHom B C) :
    spectrumComap (g.comp f) = spectrumComap f ∘ spectrumComap g := by
  funext P
  apply Subtype.ext
  apply Order.Ideal.ext
  ext a
  rfl

end PrimeIdealSpectrum

end SpectralStoneDuality
