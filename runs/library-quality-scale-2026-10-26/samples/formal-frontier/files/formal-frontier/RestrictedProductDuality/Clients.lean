/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.CharacterReconstruction
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Restricted-product duality clients

These examples exercise the compact-stage and character-reconstruction theorems for empty,
nonempty finite, and genuinely infinite index types.

The cyclic bicharacter composes mathlib's `AddChar.zmodHom` from
`Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality` (Yaël Dillies and
Bhavik Mehta) with `AddChar.toMonoidHomMulEquiv` from
`Mathlib.Algebra.Group.AddChar` (Michael Stoll). Those upstream Apache-2.0
definitions are imported, not bundled in this repository.
-/

public section

set_option warningAsError true

noncomputable section

open Set
open scoped RestrictedProduct

/-- The compact-stage theorem also applies when the index type is empty. -/
private theorem compactStage_emptyIndex
    {K : Set (Πʳ _i : Empty, [Bool, ({false} : Set Bool)])} (hK : IsCompact K) :
    ∃ s : Finset Empty,
      K ⊆ RestrictedProduct.cofiniteStage (R := fun _ : Empty ↦ Bool)
        (A := fun _ ↦ ({false} : Set Bool)) s :=
  RestrictedProduct.exists_subset_cofiniteStage (fun _ ↦ isOpen_discrete _) hK

/-- A nonempty finite index type requires no countability hypothesis. -/
private theorem compactStage_finiteIndex
    {K : Set (Πʳ _i : Fin 3, [Bool, ({false} : Set Bool)])} (hK : IsCompact K) :
    ∃ s : Finset (Fin 3),
      K ⊆ RestrictedProduct.cofiniteStage (R := fun _ : Fin 3 ↦ Bool)
        (A := fun _ ↦ ({false} : Set Bool)) s :=
  RestrictedProduct.exists_subset_cofiniteStage (fun _ ↦ isOpen_discrete _) hK

/-- The same compact-stage result also works for an infinite index type. -/
private theorem compactStage_infiniteIndex
    {K : Set (Πʳ _i : ℕ, [Bool, ({false} : Set Bool)])} (hK : IsCompact K) :
    ∃ s : Finset ℕ,
      K ⊆ RestrictedProduct.cofiniteStage (R := fun _ : ℕ ↦ Bool)
        (A := fun _ ↦ ({false} : Set Bool)) s :=
  RestrictedProduct.exists_subset_cofiniteStage (fun _ ↦ isOpen_discrete _) hK

namespace RestrictedProduct

open Multiplicative

/-- The unique bicharacter between trivial groups, used to exercise index-size edge cases. -/
@[expose] def punitBicharacter : PUnit →* PUnit →* Circle := 1

/-- The trivial bicharacter is locally perfect because both its source and character group are
singletons. -/
theorem punitBicharacter_perfect : Function.Bijective (rightCharacter punitBicharacter) := by
  constructor
  · intro y y' _
    exact Subsingleton.elim y y'
  · intro χ
    refine ⟨1, ?_⟩
    apply MonoidHom.ext
    intro x
    cases x
    exact χ.map_one.symm

/-- The full subgroup of the trivial group is its own right annihilator. -/
theorem punit_rightAnnihilator :
    (⊤ : Subgroup PUnit) = rightAnnihilator (⊤ : Subgroup PUnit) punitBicharacter := by
  ext y
  constructor
  · intro _
    rw [mem_rightAnnihilator]
    intro x _
    cases x
    cases y
    simp [punitBicharacter]
  · intro _
    simp

/-- The standard symmetric bicharacter on a finite cyclic group, in multiplicative notation. -/
@[expose] def zmodBicharacter (n : ℕ) [NeZero n] :
    Multiplicative (ZMod n) →* Multiplicative (ZMod n) →* Circle :=
  AddChar.toMonoidHomMulEquiv.toMonoidHom.comp
    (AddChar.toMonoidHom (AddChar.zmodHom (n := n)) :
      Multiplicative (ZMod n) →* AddChar (ZMod n) Circle)

@[simp]
theorem zmodBicharacter_apply (n : ℕ) [NeZero n]
    (x y : Multiplicative (ZMod n)) :
    zmodBicharacter n x y = AddChar.zmod n x.toAdd y.toAdd :=
  rfl

/-- The standard cyclic bicharacter induces the actual bijection onto circle-valued
characters. -/
theorem zmodBicharacter_perfect (n : ℕ) [NeZero n] :
    Function.Bijective (rightCharacter (zmodBicharacter n)) := by
  have hz : Function.Bijective (AddChar.zmod n) := by
    let _ : Fintype (AddChar (ZMod n) Circle) :=
      Fintype.ofEquiv (AddChar (ZMod n) ℂ) AddChar.circleEquivComplex.symm.toEquiv
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨AddChar.zmod_injective, ?_⟩
    exact (AddChar.card_eq.symm).trans
      (Fintype.card_congr AddChar.circleEquivComplex.symm.toEquiv)
  constructor
  · intro y y' h
    change y.toAdd = y'.toAdd
    apply AddChar.zmod_injective
    apply AddChar.toMonoidHomEquiv.injective
    apply MonoidHom.ext
    intro x
    have hx := DFunLike.congr_fun h x
    change zmodBicharacter n x y = zmodBicharacter n x y' at hx
    rw [zmodBicharacter_apply, zmodBicharacter_apply] at hx
    simpa [AddChar.zmod, mul_comm] using hx
  · intro χ
    obtain ⟨y, hy⟩ := hz.surjective (AddChar.toMonoidHomEquiv.symm χ)
    refine ⟨Multiplicative.ofAdd y, ?_⟩
    apply MonoidHom.ext
    intro x
    have hx := DFunLike.congr_fun hy x.toAdd
    rw [rightCharacter_apply, zmodBicharacter_apply]
    change AddChar.zmod n x.toAdd y = χ x
    rw [show AddChar.zmod n x.toAdd y = AddChar.zmod n y x.toAdd by
      simp [AddChar.zmod, mul_comm]]
    simpa using hx

/-- The discrete topology for the cyclic client coordinates, scoped to this file. -/
private local instance zmodTwoTopologicalSpaceClients :
    TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
/-- The discrete-topology witness for the cyclic client coordinates. -/
private local instance zmodTwoDiscreteTopologyClients :
    DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩

/-- The trivial-group equivalence checks the empty-index case only. -/
private noncomputable def punitDuality_emptyIndex :
    (Πʳ _i : Empty, [PUnit, (⊤ : Subgroup PUnit)]) ≃ₜ*
      PontryaginDual (Πʳ _i : Empty, [PUnit, (⊤ : Subgroup PUnit)]) := by
  apply pontryaginDualEquiv (e := fun _ ↦ punitBicharacter)
  · simp [punitBicharacter]
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ continuous_of_discreteTopology
  · exact fun _ ↦ punitBicharacter_perfect
  · exact fun _ ↦ punit_rightAnnihilator

/-- The nontrivial cyclic pairing supplies a finite-index equivalence. -/
private noncomputable def zmodDuality_finiteIndex :
    (Πʳ _i : Fin 3,
      [Multiplicative (ZMod 2), (⊤ : Subgroup (Multiplicative (ZMod 2)))]) ≃ₜ*
      PontryaginDual (Πʳ _i : Fin 3,
        [Multiplicative (ZMod 2), (⊥ : Subgroup (Multiplicative (ZMod 2)))]) := by
  apply pontryaginDualEquiv (e := fun _ ↦ zmodBicharacter 2)
  · intro i x hx y hy
    rw [Subgroup.mem_bot] at hx
    subst x
    simp
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ continuous_of_discreteTopology
  · exact fun _ ↦ zmodBicharacter_perfect 2
  · intro i
    ext y
    simp [rightAnnihilator]

/-- The nontrivial cyclic pairing supplies an infinite-index equivalence. -/
private noncomputable def zmodDuality_infiniteIndex :
    (Πʳ _i : ℕ,
      [Multiplicative (ZMod 2), (⊤ : Subgroup (Multiplicative (ZMod 2)))]) ≃ₜ*
      PontryaginDual (Πʳ _i : ℕ,
        [Multiplicative (ZMod 2), (⊥ : Subgroup (Multiplicative (ZMod 2)))]) := by
  apply pontryaginDualEquiv (e := fun _ ↦ zmodBicharacter 2)
  · intro i x hx y hy
    rw [Subgroup.mem_bot] at hx
    subst x
    simp
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ continuous_of_discreteTopology
  · exact fun _ ↦ zmodBicharacter_perfect 2
  · intro i
    ext y
    simp [rightAnnihilator]

end RestrictedProduct
