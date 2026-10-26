/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Contractibility and local path connectedness of finite simplices

The standard real simplex on a finite nonempty index type is contractible,
and hence simply connected by `SimplyConnectedSpace.ofContractible`.
Local path connectedness does not require the index type to be nonempty.

The topology is Mathlib's topology on finitely supported convex weights.
For a finite index type, `StdSimplex.isEmbedding_toFun_comp_weights` identifies
it with its convex range in the space of real-valued functions;
`StdSimplex.range_toFun_comp_weights` describes that range by nonnegative
coordinates and total mass one. The relevant general results are
`Convex.contractibleSpace` and `Convex.locallyPathConnectedSpace`.

## References

These instances use Mathlib's convex-weight model of the standard simplex and
its topology, developed by Joël Riou.
-/

@[expose] public section

namespace Convexity.StdSimplex

universe u

private lemma convex_range_weights (ι : Type u) [Finite ι] :
    Convex ℝ (Set.range (fun t ↦ t.weights : StdSimplex ℝ ι → ι → ℝ)) := by
  classical
  let := Fintype.ofFinite ι
  rw [range_toFun_comp_weights]
  refine (convex_iInter fun i : ι ↦
    convex_halfSpace_ge (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ).isLinear 0).inter ?_
  simpa only [LinearMap.sum_apply, LinearMap.proj_apply] using
    (convex_hyperplane
      (∑ i, (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)).isLinear (1 : ℝ))

/-- A real standard simplex on a finite nonempty index type is contractible. -/
instance contractibleSpace (ι : Type u) [Finite ι] [Nonempty ι] :
    ContractibleSpace (StdSimplex ℝ ι) := by
  let := (convex_range_weights ι).contractibleSpace
    (Set.range_nonempty (fun t ↦ t.weights : StdSimplex ℝ ι → ι → ℝ))
  exact (isEmbedding_toFun_comp_weights ℝ ι).toHomeomorph.contractibleSpace

/-- A real standard simplex on a finite index type is locally path connected,
including the empty simplex. -/
instance locallyPathConnectedSpace (ι : Type u) [Finite ι] :
    LocallyPathConnectedSpace (StdSimplex ℝ ι) := by
  let := (convex_range_weights ι).locallyPathConnectedSpace
  exact (isEmbedding_toFun_comp_weights ℝ ι).toHomeomorph.symm.locallyPathConnectedSpace

end Convexity.StdSimplex
