/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Constructions

/-!
# Quotients of dependent products by product ideals

For an arbitrary dependent family of commutative rings, quotienting the product
by a product ideal is canonically equivalent to the product of the coordinate
quotients.  With topological-ring structures this ring equivalence is also a
continuous additive equivalence.  The topological statement uses the open
quotient maps on both sides and imposes no separation, compactness, closedness,
finiteness, or nonemptiness assumption.

## References

- Mathlib, `Mathlib.RingTheory.Ideal.Maps`, `Mathlib.RingTheory.Ideal.Quotient.Operations`
  and `Mathlib.Topology.Algebra.Ring.Ideal` (coordinate quotient rings and quotient
  topology).
-/

@[expose] public section

universe u v

namespace Ideal

/-- The coordinate quotient homomorphism from a dependent product of rings to
the product of the coordinate quotients. -/
def piQuotientMap {ι : Type u} {R : ι → Type v} [∀ i, CommRing (R i)]
    (I : ∀ i, Ideal (R i)) : (∀ i, R i) →+* (∀ i, (R i ⧸ I i)) :=
  RingHom.pi fun i ↦
    (Ideal.Quotient.mk (I i)).comp (Pi.evalRingHom R i)

/-- The coordinate quotient map acts pointwise. -/
@[simp]
theorem piQuotientMap_apply {ι : Type u} {R : ι → Type v}
    [∀ i, CommRing (R i)] (I : ∀ i, Ideal (R i))
    (x : ∀ i, R i) (i : ι) :
    piQuotientMap I x i = Ideal.Quotient.mk (I i) (x i) :=
  rfl

/-- The coordinate quotient map is surjective, including for an empty index
type. -/
theorem piQuotientMap_surjective {ι : Type u} {R : ι → Type v}
    [∀ i, CommRing (R i)] (I : ∀ i, Ideal (R i)) :
    Function.Surjective (piQuotientMap I) := by
  intro y
  choose x hx using fun i ↦ Ideal.Quotient.mk_surjective (y i)
  exact ⟨x, funext hx⟩

/-- The kernel of the coordinate quotient map is the product ideal. -/
theorem ker_piQuotientMap {ι : Type u} {R : ι → Type v}
    [∀ i, CommRing (R i)] (I : ∀ i, Ideal (R i)) :
    RingHom.ker (piQuotientMap I) = Ideal.pi I := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_pi]
  constructor
  · intro h i
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun h i)
  · intro h
    funext i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h i)

/-- Quotienting a dependent product by a product ideal is canonically
equivalent to the dependent product of the coordinate quotients. -/
noncomputable def piQuotientRingEquiv {ι : Type u} {R : ι → Type v}
    [∀ i, CommRing (R i)] (I : ∀ i, Ideal (R i)) :
    ((∀ i, R i) ⧸ Ideal.pi I) ≃+* (∀ i, (R i ⧸ I i)) :=
  (Ideal.quotEquivOfEq (ker_piQuotientMap I).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := piQuotientMap I)
      (piQuotientMap_surjective I))

/-- The canonical product-quotient ring equivalence sends a quotient class to
the tuple of its coordinate quotient classes. -/
@[simp]
theorem piQuotientRingEquiv_mk_apply {ι : Type u} {R : ι → Type v}
    [∀ i, CommRing (R i)] (I : ∀ i, Ideal (R i))
    (x : ∀ i, R i) (i : ι) :
    piQuotientRingEquiv I (Ideal.Quotient.mk (Ideal.pi I) x) i =
      Ideal.Quotient.mk (I i) (x i) := by
  simp [piQuotientRingEquiv]

/-- The underlying map of the canonical product-quotient ring equivalence is
induced by the coordinate quotient homomorphism. -/
@[simp]
theorem piQuotientRingEquiv_mk {ι : Type u} {R : ι → Type v}
    [∀ i, CommRing (R i)] (I : ∀ i, Ideal (R i))
    (x : ∀ i, R i) :
    piQuotientRingEquiv I (Ideal.Quotient.mk (Ideal.pi I) x) =
      fun i ↦ Ideal.Quotient.mk (I i) (x i) := by
  funext i
  exact piQuotientRingEquiv_mk_apply I x i

/-- The product map of the coordinate quotient maps is an open quotient map. -/
theorem isOpenQuotientMap_piQuotientMap {ι : Type u} {R : ι → Type v}
    [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)]
    [∀ i, IsTopologicalRing (R i)] (I : ∀ i, Ideal (R i)) :
    IsOpenQuotientMap (piQuotientMap I) := by
  change IsOpenQuotientMap
    (Pi.map fun i ↦ (Ideal.Quotient.mk (I i) : R i → (R i ⧸ I i)))
  exact IsOpenQuotientMap.piMap fun i ↦
    QuotientRing.isOpenQuotientMap_mk (I i)

/-- The canonical product-quotient ring equivalence is continuous. -/
theorem continuous_piQuotientRingEquiv {ι : Type u} {R : ι → Type v}
    [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)]
    [∀ i, IsTopologicalRing (R i)] (I : ∀ i, Ideal (R i)) :
    Continuous (piQuotientRingEquiv I) := by
  rw [← (QuotientRing.isOpenQuotientMap_mk (Ideal.pi I)).continuous_comp_iff]
  have hcomp :
      (piQuotientRingEquiv I : ((∀ i, R i) ⧸ Ideal.pi I) →
          (∀ i, (R i ⧸ I i))) ∘ Ideal.Quotient.mk (Ideal.pi I) =
        piQuotientMap I := by
    funext x
    exact piQuotientRingEquiv_mk I x
  rw [hcomp]
  exact (isOpenQuotientMap_piQuotientMap I).continuous

/-- The inverse of the canonical product-quotient ring equivalence is
continuous. -/
theorem continuous_piQuotientRingEquiv_symm
    {ι : Type u} {R : ι → Type v} [∀ i, CommRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    (I : ∀ i, Ideal (R i)) :
    Continuous (piQuotientRingEquiv I).symm := by
  rw [← (isOpenQuotientMap_piQuotientMap I).continuous_comp_iff]
  have hcomp :
      ((piQuotientRingEquiv I).symm : (∀ i, (R i ⧸ I i)) →
          ((∀ i, R i) ⧸ Ideal.pi I)) ∘ piQuotientMap I =
        Ideal.Quotient.mk (Ideal.pi I) := by
    funext x
    change (piQuotientRingEquiv I).symm (piQuotientMap I x) =
      Ideal.Quotient.mk (Ideal.pi I) x
    calc
      _ = (piQuotientRingEquiv I).symm
          (piQuotientRingEquiv I (Ideal.Quotient.mk (Ideal.pi I) x)) :=
        congrArg (piQuotientRingEquiv I).symm
          (piQuotientRingEquiv_mk I x).symm
      _ = _ := (piQuotientRingEquiv I).symm_apply_apply _
  rw [hcomp]
  exact (QuotientRing.isOpenQuotientMap_mk (Ideal.pi I)).continuous

/-- The topological form of the canonical product-ideal quotient
equivalence.  Its underlying additive equivalence is the one induced by
`piQuotientRingEquiv`.

Uses Mathlib’s ideal quotients, quotient topology and product-ring maps; no printed
procyclic theorem is asserted for this general comparison. -/
noncomputable def piQuotientContinuousAddEquiv
    {ι : Type u} {R : ι → Type v} [∀ i, CommRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    (I : ∀ i, Ideal (R i)) :
    ((∀ i, R i) ⧸ Ideal.pi I) ≃ₜ+ (∀ i, (R i ⧸ I i)) :=
  ContinuousAddEquiv.mk (piQuotientRingEquiv I).toAddEquiv
    (continuous_piQuotientRingEquiv I)
    (continuous_piQuotientRingEquiv_symm I)

/-- The continuous additive and ring equivalences have the same underlying
map. -/
@[simp]
theorem piQuotientContinuousAddEquiv_apply
    {ι : Type u} {R : ι → Type v} [∀ i, CommRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    (I : ∀ i, Ideal (R i)) (x : (∀ i, R i) ⧸ Ideal.pi I) :
    piQuotientContinuousAddEquiv I x = piQuotientRingEquiv I x :=
  rfl

/-- Quotient representatives are sent coordinatewise by the continuous
additive equivalence. -/
@[simp]
theorem piQuotientContinuousAddEquiv_mk_apply
    {ι : Type u} {R : ι → Type v} [∀ i, CommRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    (I : ∀ i, Ideal (R i)) (x : ∀ i, R i) (i : ι) :
    piQuotientContinuousAddEquiv I
        (Ideal.Quotient.mk (Ideal.pi I) x) i =
      Ideal.Quotient.mk (I i) (x i) := by
  exact piQuotientRingEquiv_mk_apply I x i

end Ideal
