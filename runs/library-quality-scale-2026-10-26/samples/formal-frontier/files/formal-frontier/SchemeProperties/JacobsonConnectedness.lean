/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.JacobsonSpace

/-!
# Connectedness and closed points of Jacobson spaces

A Jacobson space is connected if and only if its subspace of closed points is
connected. No separation, finiteness, compactness or nonemptiness assumption is
imposed. In particular, this comparison applies to schemes locally of finite type
over a field via Mathlib's `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`.

The Jacobson hypothesis is substantive: the spectrum of a semilocal domain with
exactly two maximal ideals is connected, but its two-point closed-point subspace
is discrete and disconnected.

## References

- J. S. Milne, *Abelian Varieties*, version 2.00, Conventions, p. v, motivates
  comparing classical varieties with their scheme-theoretic spaces. The result
  here is an independent topological comparison, not a named theorem of that text.
- Mathlib's Jacobson-space API, including `closure_closedPoints` and
  `nonempty_inter_closedPoints`, and its connectedness API, including
  `IsConnected.closure` and `isPreconnected_closed_iff`.
-/

@[expose] public section

universe u

/-- A Jacobson space is connected exactly when its subspace of closed points is
connected. This includes the empty space, for which both sides are false. -/
theorem JacobsonSpace.connectedSpace_closedPoints_iff
    {X : Type u} [TopologicalSpace X] [JacobsonSpace X] :
    ConnectedSpace ↥(closedPoints X) ↔ ConnectedSpace X := by
  constructor
  · intro h
    rw [← isConnected_iff_connectedSpace] at h
    rw [connectedSpace_iff_univ, ← closure_closedPoints (X := X)]
    exact h.closure
  · intro h
    let := h
    apply Subtype.connectedSpace
    refine ⟨(dense_iff_closure_eq.mpr (closure_closedPoints (X := X))).nonempty, ?_⟩
    rw [isPreconnected_closed_iff]
    rintro u v hu hv hcover ⟨x, -, hxu⟩ ⟨y, -, hyv⟩
    -- A closed cover of the dense closed-point set covers the whole space.
    have hcover' : (Set.univ : Set X) ⊆ u ∪ v := by
      rw [← closure_closedPoints (X := X)]
      exact closure_minimal hcover (hu.union hv)
    obtain ⟨z, -, hzuv⟩ := isPreconnected_closed_iff.mp
      (isPreconnected_univ : IsPreconnected (Set.univ : Set X))
      u v hu hv hcover' ⟨x, Set.mem_univ _, hxu⟩ ⟨y, Set.mem_univ _, hyv⟩
    -- The nonempty closed intersection contains a globally closed point.
    obtain ⟨w, hwuv, hwc⟩ := nonempty_inter_closedPoints ⟨z, hzuv⟩
      (hu.inter hv).isLocallyClosed
    exact ⟨w, hwc, hwuv⟩
