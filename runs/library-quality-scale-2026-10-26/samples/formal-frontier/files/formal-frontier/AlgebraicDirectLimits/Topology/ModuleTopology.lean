/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Module topology under continuous linear injections

A continuous injective linear map into a semisimple module with the module
topology forces the source to have the module topology and is an embedding.
The target is an additive commutative group, as required by `IsSemisimpleModule`.
Both conclusions concern the given topologies and module structures. The source
is only an additive commutative monoid with continuous addition and scalar
multiplication; no continuity of the ring operations, separation axiom or
dimension bound is required.

Over a semisimple ring, the corollaries with suffix `_of_isSemisimpleRing` retain
additive commutative monoids on both source and target. Division rings satisfy
`IsSemisimpleRing`, so these corollaries apply to vector spaces without a separate
specialization.

## References

The module topology and its continuity API are due to Kevin Buzzard and Will Sawin
in Mathlib's `Topology.Algebra.Module.ModuleTopology`. The semisimple-module API
is due to Aaron Anderson in Mathlib's `RingTheory.SimpleModule.Basic`.
-/

@[expose] public section

universe uR uM uN

section SemisimpleTarget

variable {R : Type uR} [Ring R] [TopologicalSpace R]
  {M : Type uM} [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousSMul R M]
  {N : Type uN} [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [IsSemisimpleModule R N] [IsModuleTopology R N]

/-- A continuous injective linear map into a semisimple module with module topology
gives the original source topology the module-topology property. The source has
continuous addition and scalar multiplication, and no inverse is part of the
hypotheses. -/
theorem IsModuleTopology.of_continuous_injective
    (j : M →ₗ[R] N) (hj : Continuous j) (hinj : Function.Injective j) :
    IsModuleTopology R M := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property j hinj (LinearMap.id : M →ₗ[R] M)
  apply IsModuleTopology.of_continuous_id
  -- Only the codomain of this continuity statement uses the canonical topology.
  have hr_cont : @Continuous N M _ (moduleTopology R M) r := by
    let : TopologicalSpace M := moduleTopology R M
    let : ContinuousAdd M := ModuleTopology.continuousAdd R M
    let : ContinuousSMul R M := ModuleTopology.continuousSMul R M
    exact IsModuleTopology.continuous_of_linearMap r
  have hcomp : r ∘ j = id := funext fun x ↦ LinearMap.congr_fun hr x
  rw [← hcomp]
  exact @Continuous.comp M N M _ _ (moduleTopology R M) j r hr_cont hj

/-- A continuous injective linear map from a topological module into a semisimple
module with module topology is an embedding for the original topologies.
No caller-supplied inverse or separation assumption is required. -/
theorem LinearMap.isEmbedding_of_isModuleTopology
    (j : M →ₗ[R] N) (hj : Continuous j) (hinj : Function.Injective j) :
    Topology.IsEmbedding j := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property j hinj (LinearMap.id : M →ₗ[R] M)
  have hleft : Function.LeftInverse r j := fun x ↦ LinearMap.congr_fun hr x
  exact hleft.isEmbedding (IsModuleTopology.continuous_of_linearMap r) hj

end SemisimpleTarget

section SemisimpleRing

variable {R : Type uR} [Ring R] [IsSemisimpleRing R] [TopologicalSpace R]
  {M : Type uM} [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousSMul R M]
  {N : Type uN} [AddCommMonoid N] [Module R N] [TopologicalSpace N]
  [IsModuleTopology R N]

/-- Over a semisimple ring, a continuous injective linear map into a module with
module topology gives the original source topology the module-topology property.
Both modules retain their given additive commutative monoid structures. -/
theorem IsModuleTopology.of_continuous_injective_of_isSemisimpleRing
    (j : M →ₗ[R] N) (hj : Continuous j) (hinj : Function.Injective j) :
    IsModuleTopology R M := by
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  exact IsModuleTopology.of_continuous_injective j hj hinj

/-- Over a semisimple ring, a continuous injective linear map from a topological
module into a module with module topology is an embedding for the original
topologies, with additive commutative monoids on both source and target. -/
theorem LinearMap.isEmbedding_of_isModuleTopology_of_isSemisimpleRing
    (j : M →ₗ[R] N) (hj : Continuous j) (hinj : Function.Injective j) :
    Topology.IsEmbedding j := by
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  exact LinearMap.isEmbedding_of_isModuleTopology j hj hinj

end SemisimpleRing
