/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.NhdsKer
public import Mathlib.Topology.Separation.Basic

/-!
# Closed points in a generization subspace

In a `T₀` space, the original point is the only closed point of the subspace
`nhdsKer {x}` of its generizations. No spectrality or sobriety is needed.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.1(a), for the closed-point observation on generizations,
  with its contextual `T₀` assumption retained explicitly.
- Mathlib, `Topology.NhdsKer` and `Topology.Separation.Basic`, for
  generizations and specialization.
-/

@[expose] public section

open Set TopologicalSpace

universe u

/-- In a `T₀` space, a point of the generization subspace of `x` is closed precisely
when it is `x`. This is the observation in Fujiwara--Kato,
*Foundations of Rigid Geometry I*, §2.1(a), using the same contextual
`T₀` assumption. -/
theorem isClosed_singleton_nhdsKer_iff {X : Type u} [TopologicalSpace X]
    [T0Space X] (x : X) (z : nhdsKer ({x} : Set X)) :
    IsClosed ({z} : Set (nhdsKer ({x} : Set X))) ↔ (z : X) = x := by
  let original : nhdsKer ({x} : Set X) :=
    ⟨x, mem_nhdsKer_singleton.mpr (specializes_refl x)⟩
  have specializes_original (point : nhdsKer ({x} : Set X)) : point ⤳ original :=
    (subtype_specializes_iff point original).mpr (mem_nhdsKer_singleton.mp point.2)
  constructor
  · intro hclosed
    have hmem : original ∈ ({z} : Set (nhdsKer ({x} : Set X))) :=
      (specializes_original z).mem_closed hclosed (by simp)
    exact (congrArg Subtype.val (Set.mem_singleton_iff.mp hmem)).symm
  · intro hz
    have heq : z = original := Subtype.ext hz
    rw [heq, ← closure_subset_iff_isClosed]
    intro point hclosure
    have horiginal : original ⤳ point := specializes_iff_mem_closure.mpr hclosure
    exact Set.mem_singleton_iff.mpr
      (horiginal.antisymm (specializes_original point)).eq.symm

/-- The original point is closed in the subspace of its generizations. -/
theorem isClosed_singleton_nhdsKer {X : Type u} [TopologicalSpace X]
    [T0Space X] (x : X) :
    IsClosed ({(⟨x, mem_nhdsKer_singleton.mpr (specializes_refl x)⟩ :
      nhdsKer ({x} : Set X))} : Set (nhdsKer ({x} : Set X))) :=
  (isClosed_singleton_nhdsKer_iff x _).mpr rfl
