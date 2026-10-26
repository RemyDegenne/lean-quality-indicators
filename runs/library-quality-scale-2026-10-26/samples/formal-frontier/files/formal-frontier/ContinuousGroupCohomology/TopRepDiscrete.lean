/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.TopRepUlift
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Instances.Discrete

/-!
# Discrete direct sums and tensor products of topological representations

The algebraic actions are `Representation.directSum` and `Representation.tprod`.
Each resulting topological representation uses the discrete topology on its
algebraic carrier. Joint continuity of the acting monoid is a separate property
from continuity of its individual operators.

## References

* Mathlib, `Representation.directSum`, `Representation.tprod`, and `TopRep`.
* ContinuousGroupCohomology, `TopRep.JointlyContinuous`.
* Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, Chapter I, §1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w z

namespace TopRep

open DirectSum TensorProduct

section DirectSum

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G : Type v} [Monoid G] {ι : Type z}
  (X : ι → TopRep.{w} k G) [∀ i, DiscreteTopology (X i)]

/-- Scalar multiplication on the algebraic direct sum is continuous when the
output is given the discrete topology. -/
theorem continuousSMul_discreteDirectSum :
    @ContinuousSMul k (⨁ i, X i) _ _ (⊥ : TopologicalSpace (⨁ i, X i)) := by
  classical
  let : TopologicalSpace (⨁ i, X i) := ⊥
  let : DiscreteTopology (⨁ i, X i) := discreteTopology_bot _
  constructor
  rw [continuous_prod_of_discrete_right]
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp only [smul_zero]; exact continuous_const
  | of i a =>
      have ha : Continuous (fun r : k => r • a) :=
        continuous_smul.comp (continuous_id.prodMk continuous_const)
      have hi : Continuous (fun r : k => DirectSum.of (fun i => X i) i (r • a)) :=
        (continuous_of_discreteTopology (f := DirectSum.of (fun i => X i) i)).comp ha
      simpa only [DirectSum.of_smul] using hi
  | add x y hx hy =>
      exact (hx.add hy).congr (fun r => (smul_add r x y).symm)

/-- The componentwise representation on an arbitrary algebraic direct sum,
equipped with the discrete topology. -/
noncomputable def discreteDirectSum : TopRep.{max z w} k G := by
  letI : TopologicalSpace (⨁ i, X i) := ⊥
  letI : DiscreteTopology (⨁ i, X i) := discreteTopology_bot _
  letI : ContinuousSMul k (⨁ i, X i) := continuousSMul_discreteDirectSum X
  let ρ : Representation k G (⨁ i, X i) :=
    Representation.directSum (fun i => (X i).ρ.toRepresentation)
  exact .of <| .ofMonoidHom {
    toFun := fun g => ContinuousLinearMap.mk (ρ g) continuous_of_discreteTopology
    map_one' := by
      apply ContinuousLinearMap.ext
      intro x
      change ρ 1 x = x
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      apply ContinuousLinearMap.ext
      intro x
      change ρ (g * h) x = ρ g (ρ h x)
      rw [map_mul]
      rfl
  }

/-- The carrier of the discrete direct sum is Mathlib's algebraic direct sum. -/
@[simp] theorem discreteDirectSum_V : (discreteDirectSum X).V = (⨁ i, X i) := rfl

/-- The output topology of the discrete direct sum is discrete. -/
instance instDiscreteTopologyDiscreteDirectSum : DiscreteTopology (discreteDirectSum X) := by
  constructor
  rfl

/-- Evaluating the direct-sum action at a coordinate evaluates the input action. -/
@[simp] theorem discreteDirectSum_ρ_apply (g : G) (x : ⨁ i, X i) (i : ι) :
    (DirectSum.coeFnAddMonoidHom (fun i => X i) ((discreteDirectSum X).ρ g x)) i =
      (X i).ρ g (x i) := by
  rfl

open scoped Classical in
/-- Acting on a direct-sum injection commutes with that injection. -/
@[simp] theorem discreteDirectSum_ρ_of (g : G) (i : ι) (a : X i) :
    (discreteDirectSum X).ρ g (DirectSum.of (fun i => X i) i a) =
      DirectSum.of (fun i => X i) i ((X i).ρ g a) := by
  change DirectSum.lmap (fun i => ((X i).ρ.toRepresentation) g)
      (DirectSum.of (fun i => X i) i a) =
    DirectSum.of (fun i => X i) i ((X i).ρ g a)
  simp
  rfl

/-- A direct-sum vector is fixed exactly when all its coordinates are fixed. -/
theorem discreteDirectSum_fixed_iff (g : G) (x : ⨁ i, X i) :
    (discreteDirectSum X).ρ g x = x ↔
      ∀ i : ι, (X i).ρ g (x i) = x i := by
  constructor
  · intro h i
    have hi := discreteDirectSum_ρ_apply X g x i
    simpa only [DirectSum.coeFnAddMonoidHom_apply, h] using hi.symm
  · intro h
    apply DirectSum.ext
    intro i
    exact (discreteDirectSum_ρ_apply X g x i).trans (h i)

/-- Jointly continuous actions on discrete summands induce a jointly continuous
action on their algebraic direct sum, with no finiteness assumption on the index.
This extends the direct-sum closure in Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, Chapter I, §1, from profinite groups and
integer modules to topologized monoids and topologized rings. -/
theorem discreteDirectSum_jointlyContinuous [TopologicalSpace G]
    [∀ i, JointlyContinuous (X i)] : JointlyContinuous (discreteDirectSum X) := by
  classical
  let : TopologicalSpace (⨁ i, X i) := (discreteDirectSum X).hV3
  constructor
  rw [continuous_prod_of_discrete_right]
  intro x
  induction x using DirectSum.induction_on with
  | zero =>
      have h : Continuous (fun _ : G => (0 : discreteDirectSum X)) := continuous_const
      exact h.congr (fun g => (map_zero ((discreteDirectSum X).ρ g)).symm)
  | of i a =>
      have htop : (discreteDirectSum X).hV3 = (inferInstance : TopologicalSpace (⨁ i, X i)) := rfl
      have ha : Continuous (fun g : G => (X i).ρ g a) :=
        (JointlyContinuous.continuous_action (X := X i)).comp
          (continuous_id.prodMk continuous_const)
      have hi : Continuous (fun g : G =>
          (DirectSum.of (fun i => X i) i ((X i).ρ g a) : discreteDirectSum X)) :=
        (continuous_of_discreteTopology (f := fun a : X i =>
          (DirectSum.of (fun i => X i) i a : discreteDirectSum X))).comp ha
      have hi' : @Continuous G (⨁ i, X i) _ (discreteDirectSum X).hV3
          (fun g => DirectSum.of (fun i => X i) i ((X i).ρ g a)) :=
        htop.symm ▸ hi
      exact hi'.congr (fun g => (discreteDirectSum_ρ_of X g i a).symm)
  | add x y hx hy =>
      exact (hx.add hy).congr (fun g => (map_add ((discreteDirectSum X).ρ g) x y).symm)

end DirectSum

section Tensor

variable {k : Type u} [CommRing k] [TopologicalSpace k]
  {G : Type v} [Monoid G]
  (X : TopRep.{w} k G) (Y : TopRep.{z} k G)
  [DiscreteTopology X] [DiscreteTopology Y]

/-- Scalar multiplication on the algebraic tensor is continuous when the
output is given the discrete topology. -/
theorem continuousSMul_discreteTensor :
    @ContinuousSMul k (X ⊗[k] Y) _ _ (⊥ : TopologicalSpace (X ⊗[k] Y)) := by
  let : TopologicalSpace (X ⊗[k] Y) := ⊥
  let : DiscreteTopology (X ⊗[k] Y) := discreteTopology_bot _
  constructor
  rw [continuous_prod_of_discrete_right]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      have ha : Continuous (fun r : k => r • a) :=
        continuous_smul.comp (continuous_id.prodMk continuous_const)
      have ht : Continuous (fun p : X × Y => p.1 ⊗ₜ[k] p.2) :=
        continuous_of_discreteTopology
      have hx : Continuous (fun r : k => (r • a) ⊗ₜ[k] b) :=
        ht.comp (ha.prodMk continuous_const)
      simpa only [TensorProduct.smul_tmul'] using hx
  | add x y hx hy =>
      exact (hx.add hy).congr (fun r => (smul_add r x y).symm)

/-- The diagonal tensor representation on the algebraic tensor product,
equipped with the discrete topology. -/
noncomputable def discreteTensor : TopRep.{max w z} k G := by
  letI : TopologicalSpace (X ⊗[k] Y) := ⊥
  letI : DiscreteTopology (X ⊗[k] Y) := discreteTopology_bot _
  letI : ContinuousSMul k (X ⊗[k] Y) := continuousSMul_discreteTensor X Y
  let ρ : Representation k G (X ⊗[k] Y) :=
    Representation.tprod X.ρ.toRepresentation Y.ρ.toRepresentation
  exact .of <| .ofMonoidHom {
    toFun := fun g => ContinuousLinearMap.mk (ρ g) continuous_of_discreteTopology
    map_one' := by
      apply ContinuousLinearMap.ext
      intro x
      change ρ 1 x = x
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      apply ContinuousLinearMap.ext
      intro x
      change ρ (g * h) x = ρ g (ρ h x)
      rw [map_mul]
      rfl
  }

/-- The carrier of the discrete tensor is Mathlib's algebraic tensor product. -/
@[simp] theorem discreteTensor_V : (discreteTensor X Y).V = X ⊗[k] Y := rfl

/-- The output topology of the discrete tensor is discrete. -/
instance instDiscreteTopologyDiscreteTensor : DiscreteTopology (discreteTensor X Y) := by
  constructor
  rfl

/-- The diagonal action on a pure tensor is the tensor of the factor actions. -/
@[simp] theorem discreteTensor_ρ_tmul (g : G) (a : X) (b : Y) :
    (discreteTensor X Y).ρ g (a ⊗ₜ[k] b) =
      (X.ρ g a) ⊗ₜ[k] (Y.ρ g b) := by
  change (Representation.tprod X.ρ.toRepresentation Y.ρ.toRepresentation) g (a ⊗ₜ[k] b) =
    (X.ρ g a) ⊗ₜ[k] (Y.ρ g b)
  simp only [Representation.tprod_apply, TensorProduct.map_tmul]
  rfl

/-- If both factors are fixed, their pure tensor is fixed. The converse need
not hold: simultaneous sign changes can cancel in a tensor. -/
theorem discreteTensor_fixed_tmul (g : G) (a : X) (b : Y)
    (ha : X.ρ g a = a) (hb : Y.ρ g b = b) :
    (discreteTensor X Y).ρ g (a ⊗ₜ[k] b) = a ⊗ₜ[k] b := by
  rw [discreteTensor_ρ_tmul, ha, hb]

/-- Jointly continuous actions on discrete factors induce a jointly continuous
diagonal action on their discrete tensor product. This extends the tensor
closure in Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter I,
§1, from profinite groups and integer modules to topologized monoids and
topologized commutative rings. -/
theorem discreteTensor_jointlyContinuous [TopologicalSpace G]
    [JointlyContinuous X] [JointlyContinuous Y] :
    JointlyContinuous (discreteTensor X Y) := by
  let : TopologicalSpace (X ⊗[k] Y) := (discreteTensor X Y).hV3
  constructor
  rw [continuous_prod_of_discrete_right]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      have ha : Continuous (fun g : G => X.ρ g a) :=
        (JointlyContinuous.continuous_action (X := X)).comp
          (continuous_id.prodMk continuous_const)
      have hb : Continuous (fun g : G => Y.ρ g b) :=
        (JointlyContinuous.continuous_action (X := Y)).comp
          (continuous_id.prodMk continuous_const)
      have htop : (discreteTensor X Y).hV3 = (inferInstance : TopologicalSpace (X ⊗[k] Y)) := rfl
      have ht : Continuous (fun p : X × Y =>
          (p.1 ⊗ₜ[k] p.2 : discreteTensor X Y)) :=
        continuous_of_discreteTopology
      have hx : Continuous (fun g : G =>
          ((X.ρ g a) ⊗ₜ[k] (Y.ρ g b) : discreteTensor X Y)) :=
        ht.comp (ha.prodMk hb)
      have hx' : @Continuous G (X ⊗[k] Y) _ (discreteTensor X Y).hV3
          (fun g => (X.ρ g a) ⊗ₜ[k] (Y.ρ g b)) :=
        htop.symm ▸ hx
      exact hx'.congr (fun g => (discreteTensor_ρ_tmul X Y g a b).symm)
  | add x y hx hy =>
      exact (hx.add hy).congr (fun g => (map_add ((discreteTensor X Y).ρ g) x y).symm)

end Tensor

end TopRep
