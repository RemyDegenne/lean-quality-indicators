/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct

/-!
# Tensor products with a discrete right factor

The scalar action on an algebraic tensor with a discrete topological right
module is jointly continuous for the bottom topology on the tensor. The left
coefficient module is purely algebraic. The corresponding one-sided tensor
object has discrete topology, without requiring discrete scalars or finite
generation of either factor.

## Scope

The canonical tensor object and its fixed-coefficient generators are those of
`TopModuleCat.tensorLeftObj`. No topology is supplied as input on the left
coefficient module.

## References

The scalar-continuity statement generalizes the discrete-tensor scalar provider
`TopRep.continuousSMul_discreteTensor` in
[Continuous Group Cohomology](https://github.com/FormalFrontier/continuous-group-cohomology),
by Formal Frontier Agents. That provider is stated for two discrete topological
representations. The present statement needs only a discrete right module and
no representation or topology on the left. The canonical one-sided topology
uses Mathlib's topological-module category and module topology, due to Richard
Hill and Andrew Yang, and the tensor API of Kenny Lau and Mario Carneiro.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uM

namespace TensorProduct

/-- The scalar action on the algebraic tensor is jointly continuous for its
bottom topology when the right module is discrete. The coefficient module has
no topology. This generalizes the discrete-tensor scalar provider of the
Continuous Group Cohomology formalization by Formal Frontier Agents from two
discrete representations to arbitrary algebraic coefficients and one discrete
topological module. -/
theorem continuousSMul_bot_of_discrete_right (R : Type uR) [CommRing R]
    [TopologicalSpace R] (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    [DiscreteTopology M] :
    @ContinuousSMul R (C ⊗[R] M) _ _ (⊥ : TopologicalSpace (C ⊗[R] M)) := by
  let : TopologicalSpace (C ⊗[R] M) := ⊥
  let : DiscreteTopology (C ⊗[R] M) := discreteTopology_bot _
  refine { continuous_smul := ?_ }
  rw [continuous_prod_of_discrete_right]
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul c m =>
      have hm : Continuous (fun r : R ↦ r • m) :=
        M.continuousSMul.continuous_smul.comp (continuous_id.prodMk continuous_const)
      have hc : Continuous (fun m' : M ↦ c ⊗ₜ[R] m') :=
        continuous_of_discreteTopology
      exact (hc.comp hm).congr (fun r ↦ TensorProduct.tmul_smul r c m)
  | add x y hx hy =>
      exact (hx.add hy).congr (fun r ↦ (smul_add r x y).symm)

end TensorProduct

namespace TopModuleCat

/-- Tensoring arbitrary algebraic coefficients with a discrete right
topological module gives a discrete one-sided tensor topology. The scalar
ring need not be discrete. The statement uses the canonical module topology
and fixed-coefficient generators of `tensorLeftObj`. -/
theorem discreteTopology_tensorLeftObj (R : Type uR) [CommRing R]
    [TopologicalSpace R] (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    [DiscreteTopology M] : DiscreteTopology (tensorLeftObj R C M) := by
  refine { eq_bot := ?_ }
  change (tensorLeftObj R C M).topologicalSpace = ⊥
  rw [tensorLeftObj_topologicalSpace]
  apply le_antisymm ?_ bot_le
  apply sInf_le
  let : TopologicalSpace (C ⊗[R] M) := ⊥
  let : DiscreteTopology (C ⊗[R] M) := discreteTopology_bot _
  refine ⟨TensorProduct.continuousSMul_bot_of_discrete_right R C M,
    @continuousAdd_of_discreteTopology _ ⊥ _ (discreteTopology_bot _), ?_⟩
  intro c
  exact continuous_iff_coinduced_le.mp
    (continuous_of_discreteTopology : Continuous ((TensorProduct.mk R C M) c))

end TopModuleCat
