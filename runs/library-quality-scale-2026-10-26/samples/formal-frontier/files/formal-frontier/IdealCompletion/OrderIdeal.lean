/-

SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.Order.Ideal

/-!
# Ideal completions of bounded distributive lattices

This file equips the order ideals of a bounded distributive lattice with their
frame structure, bundles the principal-ideal embedding, and characterizes the
compact elements as the principal ideals.
-/

@[expose] public section

open Set

universe u

namespace Order.Ideal

variable {A : Type u} [DistribLattice A] [BoundedOrder A]

/-- The principal-ideal embedding as a bounded lattice homomorphism. -/
def principalHom : BoundedLatticeHom A (Ideal A) where
  toFun := principal
  map_sup' a b := by
    apply Ideal.ext
    ext x
    constructor
    · intro hx
      exact ⟨a, mem_principal_self, b, mem_principal_self, hx⟩
    · rintro ⟨i, hi, j, hj, hx⟩
      exact hx.trans (sup_le_sup hi hj)
  map_inf' a b := by
    apply Ideal.ext
    ext x
    exact le_inf_iff
  map_top' := principal_top
  map_bot' := principal_bot

/-- The principal-ideal bounded lattice homomorphism is injective. -/
theorem principalHom_injective : Function.Injective (principalHom : A → Ideal A) := by
  intro a b hab
  change principal a = principal b at hab
  apply le_antisymm
  · apply mem_principal.mp
    rw [← hab]
    exact mem_principal_self
  · apply mem_principal.mp
    rw [hab]
    exact mem_principal_self

private def sSupUpperBound (S : Set (Ideal A)) : Ideal A where
  carrier := {x | ∃ t : Finset A,
    (∀ a ∈ t, ∃ I ∈ S, a ∈ I) ∧ x ≤ t.sup id}
  nonempty' := ⟨⊥, ∅, by simp⟩
  directed' := by
    classical
    rintro x ⟨tx, htx, hx⟩ y ⟨ty, hty, hy⟩
    refine ⟨tx.sup id ⊔ ty.sup id, ?_, hx.trans le_sup_left, hy.trans le_sup_right⟩
    refine ⟨tx ∪ ty, ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact htx a ha
      · exact hty a ha
    · rw [Finset.sup_union]
  lower' := by
    rintro x y hxy ⟨t, ht, hy⟩
    exact ⟨t, ht, hxy.trans hy⟩

/-- Membership in a supremum of order ideals is witnessed by a finite join of
elements drawn from those ideals. -/
theorem mem_sSup_iff {S : Set (Ideal A)} {x : A} :
    x ∈ sSup S ↔
      ∃ t : Finset A, (∀ a ∈ t, ∃ I ∈ S, a ∈ I) ∧ x ≤ t.sup id := by
  constructor
  · intro hx
    have hle : sSup S ≤ sSupUpperBound S := by
      apply sSup_le
      intro I hI a ha
      exact ⟨{a}, by simpa using ⟨I, hI, ha⟩, by simp⟩
    exact hle hx
  · rintro ⟨t, ht, hx⟩
    apply (sSup S).lower hx
    apply (finsetSup_mem_iff (t := sSup S) (s := t) (f := id)).2
    intro a ha
    obtain ⟨I, hIS, haI⟩ := ht a ha
    exact mem_of_mem_of_le haI (le_sSup hIS)

/-- The ideal completion of a bounded distributive lattice is a frame, also
known as a complete Heyting algebra. -/
instance : Order.Frame (Ideal A) :=
  Order.Frame.ofMinimalAxioms {
    inf_sSup_le_iSup_inf := by
      intro I S x hx
      obtain ⟨t, ht, hxt⟩ := mem_sSup_iff.mp hx.2
      have hfin : t.sup (fun a => x ⊓ a) ∈ ⨆ J ∈ S, I ⊓ J := by
        apply (finsetSup_mem_iff
          (t := ⨆ J ∈ S, I ⊓ J) (s := t) (f := fun a => x ⊓ a)).2
        intro a ha
        obtain ⟨J, hJS, haJ⟩ := ht a ha
        have hxa : x ⊓ a ∈ I ⊓ J :=
          ⟨I.lower inf_le_left hx.1, J.lower inf_le_right haJ⟩
        exact mem_of_mem_of_le hxa
          (le_iSup_of_le J (le_iSup_of_le hJS le_rfl))
      rw [show x = t.sup (fun a => x ⊓ a) from
        (left_eq_inf.mpr hxt).trans (Finset.sup_inf_distrib_left t id x)]
      exact hfin }

/-- Every principal ideal is a compact element of the ideal completion. -/
theorem isCompactElement_principal (a : A) : IsCompactElement (principal a) := by
  rw [isCompactElement_iff_exists_le_sSup_of_le_sSup]
  intro S hle
  classical
  have ha : a ∈ sSup S := principal_le_iff.mp hle
  obtain ⟨t, ht, hat⟩ := mem_sSup_iff.mp ha
  let f : {x // x ∈ t} → Ideal A := fun x => Classical.choose (ht x x.property)
  have hfS (x : {x // x ∈ t}) : f x ∈ S := (Classical.choose_spec (ht x x.property)).1
  have hxf (x : {x // x ∈ t}) : x.1 ∈ f x := (Classical.choose_spec (ht x x.property)).2
  let T : Finset (Ideal A) := t.attach.image f
  refine ⟨T, ?_, ?_⟩
  · intro I hI
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hI
    exact hfS x
  · apply principal_le_iff.mpr
    apply (T.sup id).lower hat
    apply (finsetSup_mem_iff (t := T.sup id) (s := t) (f := id)).2
    intro x hx
    let x' : {x // x ∈ t} := ⟨x, hx⟩
    apply mem_of_mem_of_le (hxf x')
    have hmem : f x' ∈ T :=
      Finset.mem_image_of_mem f (Finset.mem_attach t x')
    exact Finset.le_sup (f := id) hmem

/-- The compact elements of an ideal completion are exactly the principal ideals. -/
theorem isCompactElement_iff_eq_principal (I : Ideal A) :
    IsCompactElement I ↔ ∃ a : A, I = principal a := by
  constructor
  · intro hI
    let S : Set (Ideal A) := principal '' (I : Set A)
    have hSne : S.Nonempty := by
      obtain ⟨a, ha⟩ := I.nonempty
      exact ⟨principal a, ⟨a, ha, rfl⟩⟩
    have hSdir : DirectedOn (· ≤ ·) S := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      refine ⟨principal (a ⊔ b), ⟨a ⊔ b, I.sup_mem ha hb, rfl⟩, ?_, ?_⟩
      · exact principal_le_iff.mpr (mem_principal.mpr le_sup_left)
      · exact principal_le_iff.mpr (mem_principal.mpr le_sup_right)
    have hsSup : sSup S = I := by
      apply le_antisymm
      · apply sSup_le
        rintro _ ⟨a, ha, rfl⟩
        exact principal_le_iff.mpr ha
      · intro a ha
        exact mem_of_mem_of_le mem_principal_self (le_sSup ⟨a, ha, rfl⟩)
    have hLUB : IsLUB S I := isLUB_iff_sSup_eq.mpr hsSup
    obtain ⟨_, ⟨a, ha, rfl⟩, hle⟩ := hI S I hSne hSdir hLUB le_rfl
    exact ⟨a, le_antisymm hle (principal_le_iff.mpr ha)⟩
  · rintro ⟨a, rfl⟩
    exact isCompactElement_principal a

/-- Every ideal completion is compactly generated. -/
instance : IsCompactlyGenerated (Ideal A) where
  exists_sSup_eq I := by
    let S : Set (Ideal A) := principal '' (I : Set A)
    refine ⟨S, ?_, ?_⟩
    · rintro _ ⟨a, _, rfl⟩
      exact isCompactElement_principal a
    · apply le_antisymm
      · apply sSup_le
        rintro _ ⟨a, ha, rfl⟩
        exact principal_le_iff.mpr ha
      · intro a ha
        exact mem_of_mem_of_le mem_principal_self (le_sSup ⟨a, ha, rfl⟩)

end Order.Ideal
