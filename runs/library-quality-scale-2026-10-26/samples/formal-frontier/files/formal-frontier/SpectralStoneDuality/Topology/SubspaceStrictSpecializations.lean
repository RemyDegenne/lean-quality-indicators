/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.GenericPointRemoval
public import Mathlib.Topology.Specialization
import Mathlib.Data.Set.Subset

/-!
# Strict specializations in a closed subspace

If the specializations of a selected point remain in a subspace, its strict
ambient specializations are indexed by the strict incidences in that subspace.
The point equations retain ambient endpoints; they do not identify functions
or neighborhoods on the ambient space with those of the subspace. Selected
points with no other generizations are open in an Alexandrov subspace.

## References

- Mathlib contributors, `Topology.Inseparable` and `Topology.Specialization`,
  for singleton closures and specialization in subtypes.
- Formal Frontier Agents, `SpectralStoneDuality.Topology.GenericPointRemoval`,
  for the indexed strict-incidence boundary and selected-point condition.
- Stefan Schröer, *A simple proof for Hochster's Theorem*, §2, motivates
  finite-space generic-point removal; the subspace index equations are
  auxiliary topology and are not stated there.
- Kazuhiro Fujiwara and Fumiharu Kato, *Foundations of Rigid Geometry I*,
  Chapter 0, §2.2, provides broader spectral-space context, not these equations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open Set TopologicalSpace

namespace Topology.GenericPointRemoval

variable {X : Type u} [TopologicalSpace X] {Z : Set X} {G : Set Z} (η : G)

/-- Reindex strict ambient specializations by strict incidences in a subspace
containing every specialization of the selected point. -/
noncomputable def ambientStrictEquivOfClosureSubset
    (hcontain : closure ({(η.1 : X)} : Set X) ⊆ Z)
    (hG : HasOnlyGenerizations G) :
    {σ : X // (η.1 : X) ⤳ σ ∧ ¬ σ ⤳ (η.1 : X)} ≃ Strict G η := by
  let forward (σ : {σ : X // (η.1 : X) ⤳ σ ∧ ¬ σ ⤳ (η.1 : X)}) : Strict G η := by
    let σZ : Z := ⟨σ.1, hcontain (Specializes.mem_closure σ.2.1)⟩
    have hnot : σZ ∉ G := by
      intro hσ
      have heq : η.1 = σZ :=
        hG ⟨σZ, hσ⟩ η.1 ((subtype_specializes_iff _ _).2 σ.2.1)
      exact σ.2.2 (Specializes.of_eq (congrArg Subtype.val heq).symm)
    exact ⟨⟨σZ, hnot⟩, (subtype_specializes_iff _ _).2 σ.2.1⟩
  let backward (τ : Strict G η) :
      {σ : X // (η.1 : X) ⤳ σ ∧ ¬ σ ⤳ (η.1 : X)} := by
    refine ⟨(τ.1.1 : X), (subtype_specializes_iff _ _).1 τ.2, ?_⟩
    intro hreverse
    have heq : τ.1.1 = η.1 :=
      hG η τ.1.1 ((subtype_specializes_iff _ _).2 hreverse)
    exact τ.1.2 (heq.symm ▸ η.2)
  exact {
    toFun := forward
    invFun := backward
    left_inv := by
      intro σ
      apply Subtype.ext
      rfl
    right_inv := by
      intro τ
      apply Subtype.ext
      apply Subtype.ext
      rfl
  }

@[simp]
theorem ambientStrictEquivOfClosureSubset_apply_val
    (hcontain : closure ({(η.1 : X)} : Set X) ⊆ Z)
    (hG : HasOnlyGenerizations G)
    (σ : {σ : X // (η.1 : X) ⤳ σ ∧ ¬ σ ⤳ (η.1 : X)}) :
    ((ambientStrictEquivOfClosureSubset η hcontain hG σ).1.1 : X) = σ.1 := rfl

@[simp]
theorem ambientStrictEquivOfClosureSubset_symm_apply_val
    (hcontain : closure ({(η.1 : X)} : Set X) ⊆ Z)
    (hG : HasOnlyGenerizations G) (τ : Strict G η) :
    ((ambientStrictEquivOfClosureSubset η hcontain hG).symm τ).1 =
      (τ.1.1 : X) := rfl

/-- The ambient-to-subspace strict-index equivalence for a closed subspace. -/
noncomputable def ambientStrictEquiv (hZ : IsClosed Z) (hG : HasOnlyGenerizations G) :
    {σ : X // (η.1 : X) ⤳ σ ∧ ¬ σ ⤳ (η.1 : X)} ≃ Strict G η :=
  ambientStrictEquivOfClosureSubset η
    (closure_minimal (Set.singleton_subset_iff.mpr η.1.2) hZ) hG

@[simp]
theorem ambientStrictEquiv_apply_val (hZ : IsClosed Z) (hG : HasOnlyGenerizations G)
    (σ : {σ : X // (η.1 : X) ⤳ σ ∧ ¬ σ ⤳ (η.1 : X)}) :
    ((ambientStrictEquiv η hZ hG σ).1.1 : X) = σ.1 :=
  ambientStrictEquivOfClosureSubset_apply_val η _ hG σ

@[simp]
theorem ambientStrictEquiv_symm_apply_val (hZ : IsClosed Z)
    (hG : HasOnlyGenerizations G) (τ : Strict G η) :
    ((ambientStrictEquiv η hZ hG).symm τ).1 = (τ.1.1 : X) :=
  ambientStrictEquivOfClosureSubset_symm_apply_val η _ hG τ

/-- A finite set containing all specializations of a point bounds its strict
ambient specialization indices, without any condition on selected points. -/
theorem finite_ambientStrict (x : X)
    (hcontain : closure ({x} : Set X) ⊆ Z) (hfinite : Z.Finite) :
    Finite {σ : X // x ⤳ σ ∧ ¬ σ ⤳ x} := by
  have hfin : Finite Z := Set.finite_coe_iff.mpr hfinite
  apply @Finite.of_injective _ Z hfin (fun σ : {σ : X // x ⤳ σ ∧ ¬ σ ⤳ x} =>
    (⟨σ.1, hcontain (Specializes.mem_closure σ.2.1)⟩ : Z))
  intro σ τ heq
  exact Subtype.ext (congrArg (fun z : Z => (z : X)) heq)

/-- Selected points with no other generizations are relatively open in an
Alexandrov subspace. -/
theorem isOpen_selected [AlexandrovDiscrete Z] (hG : HasOnlyGenerizations G) :
    IsOpen G := by
  apply isOpen_iff_forall_specializes.mpr
  intro x y hxy hy
  rw [hG ⟨y, hy⟩ x hxy]
  exact hy

/-- The remainder of a closed subspace after removing relatively open selected
points is closed in the ambient space. -/
theorem isClosed_remainder [AlexandrovDiscrete Z] (hZ : IsClosed Z)
    (hG : HasOnlyGenerizations G) : IsClosed (Z \ (Subtype.val '' G)) := by
  simpa only [Set.image_val_compl] using
    hZ.isClosedMap_subtype_val (Gᶜ : Set Z) ((isOpen_selected hG).isClosed_compl)

end Topology.GenericPointRemoval
