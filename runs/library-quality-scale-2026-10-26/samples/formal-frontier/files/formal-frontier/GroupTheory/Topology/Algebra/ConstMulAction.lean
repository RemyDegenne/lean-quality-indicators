/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Constant actions on coinduced spaces

An equivariant coinducing map transports continuity of each fixed scalar action
from its source to its target. The scalar type needs neither a topology nor
multiplication or action laws, and the map need not be surjective. The additive
form transports continuity of fixed vector additions under the same assumptions.

## Implementation notes

The equivariant maps and continuity classes are Mathlib's existing interfaces.
The transport uses the universal property of the coinduced topology; it defines
no new action or quotient. The characteristic conclusion is accessed through
`continuous_const_smul` or `continuous_const_vadd`.

## References

Mathlib supplies `MulActionHom`, `AddActionHom`, `ContinuousConstSMul`,
`ContinuousConstVAdd`, `Topology.IsCoinducing` and `continuous_coinduced_dom`.
-/

@[expose] public section

open scoped Topology

universe u v w

/-- Continuity of fixed scalar actions descends along an equivariant coinducing
map. No scalar topology, action laws or surjectivity is required. -/
@[to_additive
/-- Continuity of fixed vector additions descends along an equivariant coinducing
map. No vector topology, action laws or surjectivity is required. -/]
theorem Topology.IsCoinducing.continuousConstSMul
    {M : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [SMul M X] [SMul M Y]
    [ContinuousConstSMul M X] (f : X →[M] Y)
    (hf : Topology.IsCoinducing (f : X → Y)) : ContinuousConstSMul M Y := by
  refine ⟨fun c => ?_⟩
  have hc : Continuous[TopologicalSpace.coinduced (f : X → Y) inferInstance,
      inferInstance] (fun y : Y => c • y) := by
    apply continuous_coinduced_dom.mpr
    simpa only [Function.comp_def, map_smul] using
      hf.continuous.comp (continuous_const_smul c)
  rwa [← hf.eq_coinduced] at hc
