/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Pointwise convergence of operators with finite-dimensional domain

For a finite-dimensional vector space with the module topology, pointwise convergence of
continuous linear maps is equivalent to convergence in the topology of bounded convergence.
In particular, for normed spaces this is convergence in the original operator norm topology.
Neither the scalar field nor either vector space needs to be complete. The target only needs
to be a topological vector space; it need not be finite dimensional, normed or Hausdorff.

`continuousWithinAt_clm_apply_of_isModuleTopology` gives the corresponding continuity criterion.
Its source-topology hypothesis cannot be dropped over an incomplete field: a finite-dimensional
space with an arbitrary norm need not have continuous basis coordinates.

## References

The proof reconstructs an operator as a finite sum of rank-one operators, using Mathlib's
`IsModuleTopology.continuous_of_linearMap`, `ContinuousLinearMap.precomp` and
`ContinuousLinearMap.toSpanSingletonCLE`. These are the module-topology and bounded-convergence
APIs developed by Kevin Buzzard, Will Sawin, Anatole Dedecker and Yury Kudryashov. The continuity
criterion generalizes `continuousWithinAt_clm_apply` in Mathlib's finite-dimensional normed-space
API by Sébastien Gouëzel; the agreement lemma below specializes it to that result's complete-field
hypotheses.
-/

public section

open Filter Module Topology

universe uκ uE uG uX

section Topological

variable {κ : Type uκ} [NontriviallyNormedField κ]
  {E : Type uE} [AddCommGroup E] [Module κ E] [TopologicalSpace E]
  [hE : IsModuleTopology κ E] [FiniteDimensional κ E]
  {G : Type uG} [AddCommGroup G] [Module κ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul κ G]

namespace ContinuousLinearMap

/-- On a finite-dimensional domain with the module topology, convergence of continuous linear
maps in the topology of bounded convergence is equivalent to pointwise convergence. For normed
spaces this uses their given norms and the usual operator norm topology. -/
theorem tendsto_iff_forall_apply_of_isModuleTopology
    {X : Type uX} {l : Filter X} {f : X → E →L[κ] G} {g : E →L[κ] G} :
    Tendsto f l (𝓝 g) ↔ ∀ u, Tendsto (fun x ↦ f x u) l (𝓝 (g u)) := by
  classical
  refine ⟨fun h u ↦ h.eval_const u, fun h ↦ ?_⟩
  let b := Module.finBasis κ E
  let c : Fin (Module.finrank κ E) → E →L[κ] κ := fun i ↦
    ⟨b.coord i, IsModuleTopology.continuous_of_linearMap (b.coord i)⟩
  let s : Fin (Module.finrank κ E) → G →L[κ] (E →L[κ] G) := fun i ↦
    ((c i).precomp G).comp
      (toSpanSingletonCLE : G ≃L[κ] (κ →L[κ] G)).toContinuousLinearMap
  have hs (a : E →L[κ] G) : (∑ i, s i (a (b i))) = a := by
    ext u
    simp only [sum_apply]
    change (∑ i, b.repr u i • a (b i)) = a u
    simpa only [map_sum, map_smul] using congrArg a (b.sum_repr u)
  have hsum : Tendsto (fun x ↦ ∑ i, s i (f x (b i))) l
      (𝓝 (∑ i, s i (g (b i)))) :=
    tendsto_finsetSum Finset.univ fun i _ ↦
      ((s i).continuous.tendsto (g (b i))).comp (h (b i))
  simpa only [hs] using hsum

end ContinuousLinearMap

/-- A family of continuous linear maps with finite-dimensional domain carrying the module
topology is continuous within a set at a point if and only if every evaluation is.
No completeness or separation hypothesis is imposed on the target. -/
theorem continuousWithinAt_clm_apply_of_isModuleTopology
    {X : Type uX} [TopologicalSpace X] {f : X → E →L[κ] G} {s : Set X} {x : X} :
    ContinuousWithinAt f s x ↔ ∀ u, ContinuousWithinAt (fun q ↦ f q u) s x :=
  ContinuousLinearMap.tendsto_iff_forall_apply_of_isModuleTopology

end Topological

section CompleteField

variable {κ : Type uκ} [NontriviallyNormedField κ] [CompleteSpace κ]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace κ E] [FiniteDimensional κ E]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace κ G]
  {X : Type uX} [TopologicalSpace X]

/-- Recovery of Mathlib's `continuousWithinAt_clm_apply` from the module-topology criterion.
The hypotheses and conclusion are those of that normed-space result. The module-topology
instance is derived for the given source norm, and neither space's norm or topology is replaced. -/
theorem continuousWithinAt_clm_apply_of_completeSpace
    {f : X → E →L[κ] G} {s : Set X} {x : X} :
    ContinuousWithinAt f s x ↔ ∀ u, ContinuousWithinAt (fun q ↦ f q u) s x :=
  continuousWithinAt_clm_apply_of_isModuleTopology
    (hE := isModuleTopologyOfFiniteDimensional (𝕜 := κ) (E := E))

end CompleteField
