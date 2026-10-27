/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Maps.Basic

/-!
# Density of maps on units

A unit-reflecting monoid homomorphism with dense range induces a dense map on units
when the target's unit coercion is an open embedding. No topology on the source monoid
is needed. We use Mathlib's canonical unit topology and unit-reflection class.
-/

@[expose] public section

universe u v

/-- A dense monoid homomorphism that reflects units has dense range on units if the
coercion from the target's units is an open embedding. -/
theorem DenseRange.units_map
    {M : Type u} {N : Type v} [Monoid M] [Monoid N] [TopologicalSpace N]
    {f : M →* N} [IsLocalHom f] (hf : DenseRange f)
    (hval : Topology.IsOpenEmbedding (Units.val : Nˣ → N)) :
    DenseRange (Units.map f) := by
  have hd : Dense ((Units.val : Nˣ → N) ⁻¹' Set.range f) :=
    Dense.preimage hf hval.isOpenMap
  refine hd.mono ?_
  rintro u ⟨m, hm⟩
  have hfm : IsUnit (f m) := ⟨u, hm.symm⟩
  obtain ⟨v, hv⟩ := (isUnit_map_iff f m).mp hfm
  refine ⟨v, Units.ext ?_⟩
  exact (Units.coe_map f v).trans ((congrArg f hv).trans hm)
