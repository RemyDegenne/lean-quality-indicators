/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Cardinalities of covering fibers

This module states local constancy of the cardinality of the point fibers of a covering map.
The total and base spaces have independent universes. Empty and infinite fibers retain their
cardinalities; no finiteness, connectedness, local path connectedness, surjectivity or
nonemptiness assumption is imposed.

The existing `IsLocallyConstant.apply_eq_of_isPreconnected` and
`IsLocallyConstant.apply_eq_of_preconnectedSpace` give the corresponding constancy statements
on preconnected subsets and preconnected bases.

## References

* Mathlib's `IsEvenlyCovered.fiberHomeomorph` in `Mathlib.Topology.Covering.Basic`, for
  comparing model fibers with point fibers, including empty fibers.
* Mathlib's `Cardinal.mk_congr` and `IsLocallyConstant` APIs.
-/

@[expose] public section

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

namespace IsCoveringMap

/-- The cardinality of the point fiber of a covering map is locally constant. -/
theorem isLocallyConstant_cardinalMk_fiber (cov : IsCoveringMap p) :
    IsLocallyConstant (fun b : B ↦ Cardinal.mk (p ⁻¹' {b})) := by
  refine (IsLocallyConstant.iff_exists_open _).2 ?_
  intro b
  rcases cov b with ⟨hdisc, U, hbU, hU, hpU, H, hH⟩
  refine ⟨U, hU, hbU, ?_⟩
  intro b' hb'U
  have h : IsEvenlyCovered p b' (p ⁻¹' {b}) :=
    ⟨hdisc, U, hb'U, hU, hpU, H, hH⟩
  exact (Cardinal.mk_congr h.fiberHomeomorph.toEquiv).symm

end IsCoveringMap
