/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension by a discrete coefficient algebra

For a commutative ring `R`, a possibly noncommutative `R`-algebra `K` and a
topological `R`-module `M`, the underlying `R`-view is precisely the one-sided
tensor object with coefficient module `K`. The `K`-view retains that topology
and uses left multiplication on the coefficient. When `K` is discrete, the
fixed-coefficient continuous maps give joint continuity of this `K`-action.
Neither coefficient finiteness nor finiteness of `M` is required.

The coefficient module stores the algebra-induced `R`-action. The left tensor
action separately stores the regular `K`-action. The unit is an `R`-linear map
into the `R`-view, not into a `K`-object with an additional global `R`-instance.
These choices remain meaningful when `R` and `K` are the same type but the
algebra map is not the identity. The views are compared by the identity
homeomorphism, not by identifying their scalar actions.

## Limitations

No continuity of the algebra map or topological-ring hypothesis on `R` is
required for this object. Arbitrary coefficient topologies,
noncentral base maps, finite-basis topological coordinates, compactness and
Hausdorff preservation are not asserted here. Mathlib's algebraic
`ModuleCat.extendScalars` comparison is restricted to commutative `K`; the basic
object, continuous maps and functor allow noncommutative `K`.

## References

This generalizes the object, morphism and unit construction of the Continuous
Group Cohomology formalization by Formal Frontier Agents, following Beacon's
original scalar-extension development. It reuses the one-sided tensor topology
and its continuous tensor maps, rather than defining another coinduced topology.
Mathlib's topological-module category is due to Richard Hill and Andrew Yang;
its tensor-product and tensor-map APIs are due to Kenny Lau and Mario Carneiro,
and its change-of-rings API is due to Jujian Zhang. The coefficient-linear
tensor API is due to Kim Morrison, Johan Commelin and Eric Wieser. The universe
interface in the prior formalization adapts Nailin Guan's module-category
universe-lift development; that interface is not copied here. The continuous-linear
and universe-lift APIs retain the credits in `Topology.TensorProduct`.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe uR uK uM uN uP

namespace TopModuleCat

section Rebundle

variable (R : Type uR) (K : Type uK)
variable [Ring R] [Ring K] [TopologicalSpace R] [TopologicalSpace K]

/-- Rebundle a topological module with a specified scalar module structure.
The carrier, additive group, topology and topological additive-group proof are retained. -/
noncomputable def withModule (N : TopModuleCat.{uM} R)
    (moduleK : Module K N)
    (hcont : @ContinuousSMul K N moduleK.toSMul _ N.topologicalSpace) :
    TopModuleCat.{uM} K where
  toModuleCat := @ModuleCat.of K _ N N.toModuleCat.isAddCommGroup moduleK
  topologicalSpace := N.topologicalSpace
  isTopologicalAddGroup := N.isTopologicalAddGroup
  continuousSMul := hcont

/-- Rebundling the scalar module structure retains the carrier. -/
@[simp]
theorem coe_withModule (N : TopModuleCat.{uM} R) (moduleK : Module K N)
    (hcont : @ContinuousSMul K N moduleK.toSMul _ N.topologicalSpace) :
    (withModule R K N moduleK hcont : Type uM) = N := rfl

/-- Rebundling uses the original additive group and the specified scalar module. -/
theorem withModule_toModuleCat (N : TopModuleCat.{uM} R) (moduleK : Module K N)
    (hcont : @ContinuousSMul K N moduleK.toSMul _ N.topologicalSpace) :
    (withModule R K N moduleK hcont).toModuleCat =
      @ModuleCat.of K _ N N.toModuleCat.isAddCommGroup moduleK := rfl

/-- Rebundling stores the specified scalar module structure. -/
theorem withModule_isModule (N : TopModuleCat.{uM} R) (moduleK : Module K N)
    (hcont : @ContinuousSMul K N moduleK.toSMul _ N.topologicalSpace) :
    (withModule R K N moduleK hcont).toModuleCat.isModule = moduleK := rfl

/-- Rebundling uses precisely the scalar action of the specified module structure. -/
theorem withModule_smul (N : TopModuleCat.{uM} R) (moduleK : Module K N)
    (hcont : @ContinuousSMul K N moduleK.toSMul _ N.topologicalSpace) (k : K) (x : N) :
    @SMul.smul K (withModule R K N moduleK hcont)
      (withModule R K N moduleK hcont).toModuleCat.isModule.toSMul k x =
        @SMul.smul K N moduleK.toSMul k x := rfl

/-- Rebundling the scalar module structure retains the topology. -/
theorem withModule_topologicalSpace (N : TopModuleCat.{uM} R) (moduleK : Module K N)
    (hcont : @ContinuousSMul K N moduleK.toSMul _ N.topologicalSpace) :
    (withModule R K N moduleK hcont).topologicalSpace = N.topologicalSpace := rfl

end Rebundle

namespace DiscreteExtendScalars

/-- The coefficient module with the `R`-action specified by the algebra structure.
Its carrier is reducibly `K`, while its module field is `Algebra.toModule`. -/
noncomputable abbrev coefficient (R : Type uR) (K : Type uK)
    [CommRing R] [Ring K] [Algebra R K] : ModuleCat.{uK} R := by
  letI : Module R K := Algebra.toModule
  exact ModuleCat.of R K

/-- The coefficient module retains the coefficient ring as its carrier. -/
@[simp]
theorem coe_coefficient (R : Type uR) (K : Type uK)
    [CommRing R] [Ring K] [Algebra R K] :
    (coefficient R K : Type uK) = K := rfl

/-- The coefficient action is multiplication by the image of the base scalar. -/
theorem coefficient_smul (R : Type uR) (K : Type uK)
    [CommRing R] [Ring K] [Algebra R K] (r : R) (c : coefficient R K) :
    r • c = algebraMap R K r * c := by
  exact Algebra.smul_def r c

/-- The regular left module, frozen without an algebra-induced base action.
This is module data, not an additional global instance. -/
@[instance_reducible]
def regularModule (K : Type uK) [Ring K] : Module K K := inferInstance

/-- The frozen regular action is left multiplication. -/
@[simp]
theorem regularModule_smul (K : Type uK) [Ring K] (k c : K) :
    @SMul.smul K K (regularModule K).toSMul k c = k * c := rfl

/-- The regular coefficient action is multiplication on the stored coefficient carrier. -/
private theorem coefficient_regularModule_smul (R : Type uR) (K : Type uK)
    [CommRing R] [Ring K] [Algebra R K] (k : K) (c : coefficient R K) :
    @SMul.smul K (coefficient R K) (regularModule K).toSMul k c = k * c :=
  regularModule_smul K k c

/-- Restricting the regular coefficient module uses multiplication by the algebra-map image. -/
private theorem restrictScalars_regular_smul (R : Type uR) (K : Type uK)
    [CommRing R] [Ring K] [Algebra R K] (r : R)
    (c : (ModuleCat.restrictScalars (algebraMap R K)).obj
      (@ModuleCat.of K _ K _ (regularModule K))) :
    r • c = (show (ModuleCat.restrictScalars (algebraMap R K)).obj
      (@ModuleCat.of K _ K _ (regularModule K)) from
        algebraMap R K r * (show K from c)) := by
  refine (ModuleCat.restrictScalars.smul_def (algebraMap R K)
    (M := @ModuleCat.of K _ K _ (regularModule K)) r c).trans ?_
  exact congrArg (fun z : K ↦
    (show (ModuleCat.restrictScalars (algebraMap R K)).obj
      (@ModuleCat.of K _ K _ (regularModule K)) from z))
      (regularModule_smul K (algebraMap R K r) (show K from c))

/-- Centrality of the algebra map makes the stored base action commute with
regular coefficient multiplication. Both actions are specified as data. -/
theorem coefficientSMulCommClass (R : Type uR) (K : Type uK)
    [CommRing R] [Ring K] [Algebra R K] :
    @SMulCommClass R K (coefficient R K)
      (coefficient R K).isModule.toSMul (regularModule K).toSMul where
  smul_comm r k c := by
    change r • (k * c) = k * (r • c)
    rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, Algebra.commutes, mul_assoc]

/-- The stored algebra action associates with regular coefficient multiplication.
The action of `R` on the intermediate coefficient ring is algebra-induced. -/
theorem coefficientIsScalarTower (R : Type uR) (K : Type uK)
    [CommRing R] [Ring K] [Algebra R K] :
    @IsScalarTower R K (coefficient R K) Algebra.toModule.toSMul
      (regularModule K).toSMul (coefficient R K).isModule.toSMul where
  smul_assoc r k c := by
    change (r • k) * c = r • (k * c)
    rw [Algebra.smul_def, Algebra.smul_def, mul_assoc]

end DiscreteExtendScalars

section Basic

variable (R : Type uR) (K : Type uK)
variable [CommRing R] [Ring K] [Algebra R K] [TopologicalSpace R]

/-- The separate bundled `R`-view of scalar extension, with the one-sided tensor topology. -/
noncomputable def discreteExtendScalarsRObj (M : TopModuleCat.{uM} R) :
    TopModuleCat.{max uK uM} R :=
  tensorLeftObj R (DiscreteExtendScalars.coefficient R K) M

/-- The `R`-view is the existing tensor object for the algebra coefficient module. -/
theorem discreteExtendScalarsRObj_eq_tensorLeftObj (M : TopModuleCat.{uM} R) :
    discreteExtendScalarsRObj R K M = tensorLeftObj R (ModuleCat.of R K) M := rfl

/-- The carrier of the `R`-view is the tensor product over the specified base action. -/
@[simp]
theorem coe_discreteExtendScalarsRObj (M : TopModuleCat.{uM} R) :
    (discreteExtendScalarsRObj R K M : Type (max uK uM)) = TensorProduct R K M := rfl

/-- The topology of the `R`-view is exactly the primitive tensor topology. -/
theorem discreteExtendScalarsRObj_topologicalSpace (M : TopModuleCat.{uM} R) :
    (discreteExtendScalarsRObj R K M).topologicalSpace =
      (tensorLeftObj R (DiscreteExtendScalars.coefficient R K) M).topologicalSpace := rfl

namespace DiscreteExtendScalars

omit [TopologicalSpace R] in
/-- The base scalar action stored by the coefficient bundle is the algebra
scalar action, hence multiplication by the algebra-map image. -/
private theorem coefficient_stored_smul (r : R) (c : coefficient R K) :
    @Eq (coefficient R K)
      (@SMul.smul R (coefficient R K) (coefficient R K).isModule.toSMul r c)
      (algebraMap R K r * c) := by
  have hs : @Eq (coefficient R K)
      (@SMul.smul R (coefficient R K) (coefficient R K).isModule.toSMul r c)
      (show coefficient R K from
        @SMul.smul R K Algebra.toModule.toSMul r (show K from c)) := rfl
  exact hs.trans (congrArg (fun z : K ↦ (show coefficient R K from z))
    (@Algebra.smul_def R K _ _ ‹Algebra R K› r (show K from c)))

omit [TopologicalSpace R] in
/-- Restriction of the canonical regular coefficient bundle has the stored
base action given by multiplication by the algebra-map image. The canonical
regular bundle and the separately specified regular module agree on their actions. -/
private theorem restrictScalars_canonical_smul (r : R)
    (c : (ModuleCat.restrictScalars (algebraMap R K)).obj (ModuleCat.of K K)) :
    @Eq ((ModuleCat.restrictScalars (algebraMap R K)).obj (ModuleCat.of K K))
      (@SMul.smul R ((ModuleCat.restrictScalars (algebraMap R K)).obj (ModuleCat.of K K))
        ((ModuleCat.restrictScalars (algebraMap R K)).obj (ModuleCat.of K K)).isModule.toSMul r c)
      (show (ModuleCat.restrictScalars (algebraMap R K)).obj (ModuleCat.of K K) from
        algebraMap R K r * (show K from c)) := by
  let C := (ModuleCat.restrictScalars (algebraMap R K)).obj (ModuleCat.of K K)
  let D := (ModuleCat.restrictScalars (algebraMap R K)).obj
    (@ModuleCat.of K _ K _ (regularModule K))
  have hs : @Eq C (@SMul.smul R C C.isModule.toSMul r c)
      (show C from @SMul.smul R D D.isModule.toSMul r (show D from c)) := rfl
  have hd : @Eq D (@SMul.smul R D D.isModule.toSMul r (show D from c))
      (show D from algebraMap R K r * (show K from c)) :=
    restrictScalars_regular_smul R K r (show D from c)
  exact hs.trans (congrArg (fun z : D ↦ (show C from z)) hd)

/-- Induction on pure tensors and sums, with the motive on the bundled base view. -/
@[elab_as_elim]
theorem rObj_inductionOn (M : TopModuleCat.{uM} R)
    {P : discreteExtendScalarsRObj R K M → Prop} (x : discreteExtendScalarsRObj R K M)
    (tmul : ∀ (c : K) (m : M), P (c ⊗ₜ[R] m))
    (add : ∀ x y : discreteExtendScalarsRObj R K M, P x → P y → P (x + y)) : P x := by
  exact TensorProduct.inductionOn
    (motive := fun z : TensorProduct R (coefficient R K) M ↦
      P (show discreteExtendScalarsRObj R K M from z)) x
    (fun c m ↦ tmul (show K from c) m)
    (fun x y hx hy ↦ add (show discreteExtendScalarsRObj R K M from x)
      (show discreteExtendScalarsRObj R K M from y) hx hy)

/-- Mathlib's left tensor module, using regular multiplication on `K` and the
algebra-induced base action stored in `coefficient`. This is a value, not an instance. -/
@[instance_reducible]
noncomputable def leftModule (M : TopModuleCat.{uM} R) :
    Module K (discreteExtendScalarsRObj R K M) := by
  letI : Module R (coefficient R K) := (coefficient R K).isModule
  letI : Module K (coefficient R K) := regularModule K
  letI : SMulCommClass R K (coefficient R K) := coefficientSMulCommClass R K
  change Module K (TensorProduct R (coefficient R K) M)
  exact TensorProduct.leftModule (R := R) (R'' := K)
    (M := coefficient R K) (N := M)

/-- The coefficient scalar action, kept separate from the bundled base action. -/
noncomputable def scalar (M : TopModuleCat.{uM} R) (k : K)
    (x : discreteExtendScalarsRObj R K M) : discreteExtendScalarsRObj R K M := by
  letI : Module K (discreteExtendScalarsRObj R K M) := leftModule R K M
  exact k • x

/-- Coefficient scalars act by multiplication on the left tensor factor. -/
@[simp]
theorem scalar_tmul (M : TopModuleCat.{uM} R) (k c : K) (m : M) :
    scalar R K M k (c ⊗ₜ[R] m) = (k * c) ⊗ₜ[R] m := by
  let : Module R (coefficient R K) := (coefficient R K).isModule
  let : Module K (coefficient R K) := regularModule K
  let : SMulCommClass R K (coefficient R K) := coefficientSMulCommClass R K
  -- Convert the carrier once, while retaining the coefficient and tensor module data.
  change @Eq (TensorProduct R (coefficient R K) M)
    (@SMul.smul K (TensorProduct R (coefficient R K) M)
      (leftModule R K M).toSMul k (c ⊗ₜ[R] m)) ((k * c) ⊗ₜ[R] m)
  exact (TensorProduct.smul_tmul' (R := R) (M := coefficient R K) (N := M) k c m).trans
    (congrArg (fun a : coefficient R K ↦ a ⊗ₜ[R] m)
      (coefficient_regularModule_smul R K k c))

/-- The stored coefficient action distributes over addition in the base view. -/
theorem scalar_add (M : TopModuleCat.{uM} R) (k : K)
    (x y : discreteExtendScalarsRObj R K M) :
    scalar R K M k (x + y) = scalar R K M k x + scalar R K M k y := by
  let : Module K (discreteExtendScalarsRObj R K M) := leftModule R K M
  exact smul_add k x y

/-- The coefficient action through the algebra map recovers the stored base action. -/
theorem scalar_algebraMap (M : TopModuleCat.{uM} R) (r : R)
    (x : discreteExtendScalarsRObj R K M) :
    scalar R K M (algebraMap R K r) x = r • x := by
  let : Module R (coefficient R K) := (coefficient R K).isModule
  let : Module K (coefficient R K) := regularModule K
  let : SMulCommClass R K (coefficient R K) := coefficientSMulCommClass R K
  let : IsScalarTower R K (coefficient R K) := coefficientIsScalarTower R K
  let : Module K (discreteExtendScalarsRObj R K M) := leftModule R K M
  let : IsScalarTower R K (discreteExtendScalarsRObj R K M) :=
    TensorProduct.isScalarTower_left (R := R) (R' := K) (R'₂ := R)
      (M := coefficient R K) (N := M)
  exact (algebra_compatible_smul K r x).symm

/-- Fixed left multiplication is realized through the `R`-linear coefficient
slot. It is not required to be `K`-linear when `K` is noncommutative. -/
noncomputable def scalarRCLM (M : TopModuleCat.{uM} R) (k : K) :
    discreteExtendScalarsRObj R K M →L[R] discreteExtendScalarsRObj R K M :=
  tensorMapCLM R (LinearMap.mulLeft R k : coefficient R K →ₗ[R] coefficient R K)
    (ContinuousLinearMap.id R M)

/-- Fixed coefficient multiplication sends a pure tensor to its left-factor product. -/
@[simp]
theorem scalarRCLM_tmul (M : TopModuleCat.{uM} R) (k c : K) (m : M) :
    scalarRCLM R K M k (c ⊗ₜ[R] m) = (k * c) ⊗ₜ[R] m := by
  exact congrArg (fun z : tensorLeftObj R (coefficient R K) M ↦
    (show discreteExtendScalarsRObj R K M from z))
      (tensorMapCLM_tmul R
        (LinearMap.mulLeft R k : coefficient R K →ₗ[R] coefficient R K)
        (ContinuousLinearMap.id R M) c m)

/-- The fixed-scalar continuous map agrees with the separately stored coefficient action. -/
theorem scalarRCLM_apply (M : TopModuleCat.{uM} R) (k : K)
    (x : discreteExtendScalarsRObj R K M) :
    scalarRCLM R K M k x = scalar R K M k x := by
  refine rObj_inductionOn R K M
    (P := fun z : discreteExtendScalarsRObj R K M ↦
      scalarRCLM R K M k z = scalar R K M k z) x ?_ ?_
  · intro c m
    exact (scalarRCLM_tmul R K M k c m).trans (scalar_tmul R K M k c m).symm
  · intro x y hx hy
    rw [(scalarRCLM R K M k).map_add, scalar_add, hx, hy]

/-- Each fixed coefficient acts continuously for the primitive topology. -/
theorem continuous_scalar (M : TopModuleCat.{uM} R) (k : K) :
    Continuous (scalar R K M k) := by
  exact (scalarRCLM R K M k).continuous.congr (scalarRCLM_apply R K M k)

/-- The continuous unit takes values in the separate bundled `R`-view. -/
noncomputable def unitContinuous (M : TopModuleCat.{uM} R) :
    M →L[R] discreteExtendScalarsRObj R K M :=
  tensorGenerator R (coefficient R K) M (show coefficient R K from (1 : K))

/-- The unit is the generator at the coefficient `1`. -/
@[simp]
theorem unitContinuous_apply (M : TopModuleCat.{uM} R) (m : M) :
    unitContinuous R K M m = (1 : K) ⊗ₜ[R] m := rfl

/-- Scalar extension in the `R`-view reuses the continuous tensor-map primitive.
The source and target carrier universes are independent. -/
noncomputable def mapRCLM {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) : discreteExtendScalarsRObj R K M →L[R]
      discreteExtendScalarsRObj R K N :=
  tensorMapCLM R (LinearMap.id : coefficient R K →ₗ[R] coefficient R K) g

/-- The underlying `R`-linear map is precisely Mathlib's ordinary tensor map. -/
@[simp]
theorem mapRCLM_toLinearMap {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) : (mapRCLM R K g).toLinearMap =
      TensorProduct.map (LinearMap.id : coefficient R K →ₗ[R] coefficient R K)
        g.toLinearMap := rfl

/-- The base-scalar tensor map sends a pure tensor to the right-factor image. -/
@[simp]
theorem mapRCLM_tmul {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) (c : K) (m : M) :
    mapRCLM R K g (c ⊗ₜ[R] m) = c ⊗ₜ[R] g m := by
  exact tensorMapCLM_tmul R (LinearMap.id : coefficient R K →ₗ[R] coefficient R K)
    g c m

/-- Pointwise agreement of the base-view map with the ordinary algebraic tensor map. -/
private theorem mapRCLM_tensorMap_apply
    {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) (x : discreteExtendScalarsRObj R K M) :
    @Eq (discreteExtendScalarsRObj R K N) (mapRCLM R K g x)
      (show discreteExtendScalarsRObj R K N from
        TensorProduct.map (LinearMap.id : coefficient R K →ₗ[R] coefficient R K)
          g.toLinearMap x) := by
  -- Both endpoints are applications of the same tensor-map function.
  rfl

/-- The base-view tensor map preserves identity continuous linear maps. -/
@[simp]
theorem mapRCLM_id (M : TopModuleCat.{uM} R) :
    mapRCLM R K (ContinuousLinearMap.id R M) =
      ContinuousLinearMap.id R (discreteExtendScalarsRObj R K M) :=
  tensorMapCLM_id R (C := coefficient R K) (M := M)

/-- The base-view tensor map preserves composition. -/
theorem mapRCLM_comp {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    {P : TopModuleCat.{uP} R} (g : M →L[R] N) (h : N →L[R] P) :
    mapRCLM R K (h.comp g) = (mapRCLM R K h).comp (mapRCLM R K g) := by
  have hp : @Eq (discreteExtendScalarsRObj R K M →L[R]
      discreteExtendScalarsRObj R K P)
      (tensorMapCLM R
        ((LinearMap.id : coefficient R K →ₗ[R] coefficient R K).comp LinearMap.id)
        (h.comp g))
      ((mapRCLM R K h).comp (mapRCLM R K g)) :=
    tensorMapCLM_comp R
      (LinearMap.id : coefficient R K →ₗ[R] coefficient R K)
      (LinearMap.id : coefficient R K →ₗ[R] coefficient R K) g h
  have hi : (LinearMap.id : coefficient R K →ₗ[R] coefficient R K).comp
      LinearMap.id = LinearMap.id := LinearMap.id_comp _
  exact (congrArg (fun f : coefficient R K →ₗ[R] coefficient R K ↦
    (show discreteExtendScalarsRObj R K M →L[R] discreteExtendScalarsRObj R K P from
      tensorMapCLM R f (h.comp g))) hi).symm.trans hp

/-- The base-view tensor map commutes with the separately stored coefficient action. -/
theorem mapRCLM_scalar {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) (k : K) (x : discreteExtendScalarsRObj R K M) :
    mapRCLM R K g (scalar R K M k x) = scalar R K N k (mapRCLM R K g x) := by
  refine rObj_inductionOn R K M
    (P := fun z : discreteExtendScalarsRObj R K M ↦
      @Eq (discreteExtendScalarsRObj R K N)
        (mapRCLM R K g (scalar R K M k z))
        (scalar R K N k (mapRCLM R K g z))) x ?_ ?_
  · intro c m
    have h₁ : @Eq (discreteExtendScalarsRObj R K N)
        (mapRCLM R K g (scalar R K M k (c ⊗ₜ[R] m)))
        (mapRCLM R K g ((k * c) ⊗ₜ[R] m)) :=
      congrArg (fun z : discreteExtendScalarsRObj R K M ↦ mapRCLM R K g z)
        (scalar_tmul R K M k c m)
    have h₂ : @Eq (discreteExtendScalarsRObj R K N)
        (mapRCLM R K g ((k * c) ⊗ₜ[R] m)) ((k * c) ⊗ₜ[R] g m) :=
      mapRCLM_tmul R K g (k * c) m
    have h₃ : @Eq (discreteExtendScalarsRObj R K N)
        ((k * c) ⊗ₜ[R] g m) (scalar R K N k (c ⊗ₜ[R] g m)) :=
      (scalar_tmul R K N k c (g m)).symm
    have h₄ : @Eq (discreteExtendScalarsRObj R K N)
        (scalar R K N k (c ⊗ₜ[R] g m))
        (scalar R K N k (mapRCLM R K g (c ⊗ₜ[R] m))) :=
      congrArg (fun z : discreteExtendScalarsRObj R K N ↦ scalar R K N k z)
        (mapRCLM_tmul R K g c m).symm
    exact h₁.trans (h₂.trans (h₃.trans h₄))
  · intro x y hx hy
    exact (congrArg (fun z : discreteExtendScalarsRObj R K M ↦ mapRCLM R K g z)
      (scalar_add R K M k x y)).trans
        (((mapRCLM R K g).map_add (scalar R K M k x) (scalar R K M k y)).trans
          ((congrArg₂ (fun a b : discreteExtendScalarsRObj R K N ↦
            @Add.add (discreteExtendScalarsRObj R K N)
              (discreteExtendScalarsRObj R K N).toModuleCat.isAddCommGroup.toAdd a b) hx hy).trans
            ((scalar_add R K N k (mapRCLM R K g x) (mapRCLM R K g y)).symm.trans
              (congrArg (fun z : discreteExtendScalarsRObj R K N ↦ scalar R K N k z)
                ((mapRCLM R K g).map_add x y).symm))))

variable [TopologicalSpace K] [DiscreteTopology K]

/-- Discreteness of `K` upgrades the fixed-scalar continuity to joint continuity. -/
theorem continuous_scalar_joint (M : TopModuleCat.{uM} R) :
    Continuous (fun p : K × discreteExtendScalarsRObj R K M ↦
      scalar R K M p.1 p.2) := by
  exact continuous_prod_of_discrete_left.mpr (continuous_scalar R K M)

-- Keep the action's continuity proof opaque when rebundling the tensor object.
private theorem continuousSMul_leftModule (M : TopModuleCat.{uM} R) :
    @ContinuousSMul K (discreteExtendScalarsRObj R K M)
      (leftModule R K M).toSMul ‹TopologicalSpace K›
      (discreteExtendScalarsRObj R K M).topologicalSpace := by
  refine @ContinuousSMul.mk K (discreteExtendScalarsRObj R K M)
    (leftModule R K M).toSMul ‹TopologicalSpace K›
    (discreteExtendScalarsRObj R K M).topologicalSpace ?_
  change Continuous (fun p : K × discreteExtendScalarsRObj R K M ↦
    scalar R K M p.1 p.2)
  exact @continuous_scalar_joint R K ‹CommRing R› ‹Ring K› ‹Algebra R K›
    ‹TopologicalSpace R› ‹TopologicalSpace K› ‹DiscreteTopology K› M

end DiscreteExtendScalars

variable [TopologicalSpace K] [DiscreteTopology K]

/-- Scalar extension as a `K`-topological module. Its module field is the
canonical left tensor module and its topology field is exactly the separate `R`-view. -/
noncomputable def discreteExtendScalarsObj (M : TopModuleCat.{uM} R) :
    TopModuleCat.{max uK uM} K :=
  TopModuleCat.withModule R K (discreteExtendScalarsRObj R K M)
    (DiscreteExtendScalars.leftModule R K M)
    (by exact DiscreteExtendScalars.continuousSMul_leftModule R K M)

/-- The coefficient-linear object retains the algebraic tensor carrier. -/
@[simp]
theorem coe_discreteExtendScalarsObj (M : TopModuleCat.{uM} R) :
    (discreteExtendScalarsObj R K M : Type (max uK uM)) = TensorProduct R K M := rfl

/-- Forgetting topology retains the canonical left tensor module. -/
theorem discreteExtendScalarsObj_toModuleCat (M : TopModuleCat.{uM} R) :
    (discreteExtendScalarsObj R K M).toModuleCat =
      ModuleCat.of K (TensorProduct R K M) := by
  rfl

/-- The coefficient view stores the separately constructed regular left tensor module. -/
theorem discreteExtendScalarsObj_isModule (M : TopModuleCat.{uM} R) :
    (discreteExtendScalarsObj R K M).toModuleCat.isModule =
      DiscreteExtendScalars.leftModule R K M := rfl

/-- The coefficient-linear and base-linear views have identical topologies. -/
theorem discreteExtendScalarsObj_topologicalSpace (M : TopModuleCat.{uM} R) :
    (discreteExtendScalarsObj R K M).topologicalSpace =
      (discreteExtendScalarsRObj R K M).topologicalSpace :=
  TopModuleCat.withModule_topologicalSpace R K (discreteExtendScalarsRObj R K M)
    (DiscreteExtendScalars.leftModule R K M)
    (by exact DiscreteExtendScalars.continuousSMul_leftModule R K M)

/-- The packaged coefficient action is the separately stored canonical left action. -/
theorem discreteExtendScalarsObj_smul (M : TopModuleCat.{uM} R) (k : K)
    (x : discreteExtendScalarsObj R K M) :
    k • x = DiscreteExtendScalars.scalar R K M k x := rfl

/-- Coefficient multiplication on a pure tensor is regular left multiplication. -/
@[simp]
theorem discreteExtendScalarsObj_smul_tmul (M : TopModuleCat.{uM} R) (k c : K) (m : M) :
    @SMul.smul K (discreteExtendScalarsObj R K M)
      (discreteExtendScalarsObj R K M).toModuleCat.isModule.toSMul k (c ⊗ₜ[R] m) =
        (k * c) ⊗ₜ[R] m := by
  exact DiscreteExtendScalars.scalar_tmul R K M k c m

namespace DiscreteExtendScalars

/-- Induction on pure tensors and sums, with the motive on the bundled coefficient view. -/
@[elab_as_elim]
theorem obj_inductionOn (M : TopModuleCat.{uM} R)
    {P : discreteExtendScalarsObj R K M → Prop} (x : discreteExtendScalarsObj R K M)
    (tmul : ∀ (c : K) (m : M), P (c ⊗ₜ[R] m))
    (add : ∀ x y : discreteExtendScalarsObj R K M, P x → P y → P (x + y)) : P x := by
  exact TensorProduct.inductionOn
    (motive := fun z : TensorProduct R (coefficient R K) M ↦
      P (show discreteExtendScalarsObj R K M from z)) x
    (fun c m ↦ tmul (show K from c) m)
    (fun x y hx hy ↦ add (show discreteExtendScalarsObj R K M from x)
      (show discreteExtendScalarsObj R K M from y) hx hy)

/-- The identity comparison retains the carrier and topology but does not
identify the base and coefficient scalar actions. -/
noncomputable def rViewHomeomorph (M : TopModuleCat.{uM} R) :
    discreteExtendScalarsRObj R K M ≃ₜ discreteExtendScalarsObj R K M where
  toEquiv :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

/-- The comparison of the two topological carriers is the identity. -/
@[simp]
theorem rViewHomeomorph_apply (M : TopModuleCat.{uM} R)
    (x : discreteExtendScalarsRObj R K M) : rViewHomeomorph R K M x = x := rfl

/-- The carrier comparison sends the separate coefficient action to the bundled action. -/
theorem rViewHomeomorph_scalar (M : TopModuleCat.{uM} R) (k : K)
    (x : discreteExtendScalarsRObj R K M) :
    @Eq (discreteExtendScalarsObj R K M)
      (rViewHomeomorph R K M (scalar R K M k x))
      (@SMul.smul K (discreteExtendScalarsObj R K M)
        (discreteExtendScalarsObj R K M).toModuleCat.isModule.toSMul k
        (rViewHomeomorph R K M x)) := rfl

/-- On corresponding carriers, the base action agrees with the coefficient
action through the specified algebra map, not through equality of scalar types. -/
theorem rViewHomeomorph_smul (M : TopModuleCat.{uM} R) (r : R)
    (x : discreteExtendScalarsRObj R K M) :
    rViewHomeomorph R K M (r • x) = algebraMap R K r • rViewHomeomorph R K M x := by
  exact (congrArg (rViewHomeomorph R K M) (scalar_algebraMap R K M r x).symm).trans
    (rViewHomeomorph_scalar R K M (algebraMap R K r) x)

/-- The tensor-map function on the coefficient view is the composite of the
base-view map with the two identity carrier comparisons. The equality is of
functions with the complete bundled source and target. -/
private theorem tensorMap_rViewHomeomorph
    {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R} (g : M →L[R] N) :
    @Eq (discreteExtendScalarsObj R K M → discreteExtendScalarsObj R K N)
      (show discreteExtendScalarsObj R K M → discreteExtendScalarsObj R K N from
        TensorProduct.map (LinearMap.id : coefficient R K →ₗ[R] coefficient R K)
          g.toLinearMap)
      (fun x : discreteExtendScalarsObj R K M ↦
        rViewHomeomorph R K N (mapRCLM R K g ((rViewHomeomorph R K M).symm x))) := by
  let F : discreteExtendScalarsObj R K M → discreteExtendScalarsObj R K N :=
    TensorProduct.map (LinearMap.id : coefficient R K →ₗ[R] coefficient R K) g.toLinearMap
  let T : discreteExtendScalarsRObj R K M → discreteExtendScalarsRObj R K N :=
    TensorProduct.map (LinearMap.id : coefficient R K →ₗ[R] coefficient R K) g.toLinearMap
  funext x
  have hb : @Eq (discreteExtendScalarsRObj R K N)
      (mapRCLM R K g ((rViewHomeomorph R K M).symm x))
      (T ((rViewHomeomorph R K M).symm x)) :=
    mapRCLM_tensorMap_apply R K g ((rViewHomeomorph R K M).symm x)
  have hc : @Eq (discreteExtendScalarsObj R K N) (F x)
      (rViewHomeomorph R K N (T ((rViewHomeomorph R K M).symm x))) := rfl
  exact hc.trans (congrArg
    (fun z : discreteExtendScalarsRObj R K N ↦ rViewHomeomorph R K N z) hb).symm

/-- Equivariance of the ordinary tensor-map function for the stored coefficient
actions follows by transporting base-view equivariance through the carrier
comparisons. No scalar structure is inferred from equality of carriers. -/
private theorem tensorMap_smul
    {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R} (g : M →L[R] N) :
    ∀ (k : K) (x : discreteExtendScalarsObj R K M),
      @Eq (discreteExtendScalarsObj R K N)
        ((show discreteExtendScalarsObj R K M → discreteExtendScalarsObj R K N from
          TensorProduct.map (LinearMap.id : coefficient R K →ₗ[R] coefficient R K)
            g.toLinearMap)
          (@SMul.smul K (discreteExtendScalarsObj R K M)
            (discreteExtendScalarsObj R K M).toModuleCat.isModule.toSMul k x))
        (@SMul.smul K (discreteExtendScalarsObj R K N)
          (discreteExtendScalarsObj R K N).toModuleCat.isModule.toSMul ((RingHom.id K) k)
          ((show discreteExtendScalarsObj R K M → discreteExtendScalarsObj R K N from
            TensorProduct.map (LinearMap.id : coefficient R K →ₗ[R] coefficient R K)
              g.toLinearMap) x)) := by
  let F : discreteExtendScalarsObj R K M → discreteExtendScalarsObj R K N :=
    TensorProduct.map (LinearMap.id : coefficient R K →ₗ[R] coefficient R K) g.toLinearMap
  let sM : K → discreteExtendScalarsObj R K M → discreteExtendScalarsObj R K M :=
    @SMul.smul K (discreteExtendScalarsObj R K M)
      (discreteExtendScalarsObj R K M).toModuleCat.isModule.toSMul
  let sN : K → discreteExtendScalarsObj R K N → discreteExtendScalarsObj R K N :=
    @SMul.smul K (discreteExtendScalarsObj R K N)
      (discreteExtendScalarsObj R K N).toModuleCat.isModule.toSMul
  refine (show ∀ (k : K) (x : discreteExtendScalarsObj R K M),
    @Eq (discreteExtendScalarsObj R K N) (F (sM k x)) (sN ((RingHom.id K) k) (F x))
      from ?_)
  intro k x
  have hF (z : discreteExtendScalarsRObj R K M) :
      @Eq (discreteExtendScalarsObj R K N)
        (F (rViewHomeomorph R K M z)) (rViewHomeomorph R K N (mapRCLM R K g z)) :=
    (congrFun (tensorMap_rViewHomeomorph R K g) (rViewHomeomorph R K M z)).trans
      (congrArg (fun y : discreteExtendScalarsRObj R K M ↦
        rViewHomeomorph R K N (mapRCLM R K g y))
          ((rViewHomeomorph R K M).symm_apply_apply z))
  have hx : @Eq (discreteExtendScalarsObj R K M) (sM k x)
      (rViewHomeomorph R K M (scalar R K M k ((rViewHomeomorph R K M).symm x))) :=
    ((rViewHomeomorph_scalar R K M k ((rViewHomeomorph R K M).symm x)).trans
      (congrArg (sM k) ((rViewHomeomorph R K M).apply_symm_apply x))).symm
  have hout : @Eq (discreteExtendScalarsObj R K N)
      (rViewHomeomorph R K N (mapRCLM R K g ((rViewHomeomorph R K M).symm x)))
      (F x) :=
    (hF ((rViewHomeomorph R K M).symm x)).symm.trans
      (congrArg F ((rViewHomeomorph R K M).apply_symm_apply x))
  have hlinear : @Eq (discreteExtendScalarsObj R K N) (F (sM k x)) (sN k (F x)) :=
    (congrArg F hx).trans
      ((hF (scalar R K M k ((rViewHomeomorph R K M).symm x))).trans
        ((congrArg (fun y : discreteExtendScalarsRObj R K N ↦ rViewHomeomorph R K N y)
          (mapRCLM_scalar R K g k ((rViewHomeomorph R K M).symm x))).trans
            ((rViewHomeomorph_scalar R K N k
              (mapRCLM R K g ((rViewHomeomorph R K M).symm x))).trans
                (congrArg (sN k) hout))))
  exact hlinear.trans (congrArg (fun a : K ↦ sN a (F x))
    (show k = (RingHom.id K) k from rfl))

/-- The ordinary tensor map with fixed left identity is coefficient-linear.
Its function is `TensorProduct.map`, not a choice of continuous realization. -/
noncomputable def mapLinear {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) : discreteExtendScalarsObj R K M →ₗ[K]
      discreteExtendScalarsObj R K N where
  toFun := TensorProduct.map (LinearMap.id : coefficient R K →ₗ[R] coefficient R K)
    g.toLinearMap
  map_add' x y := (mapRCLM R K g).map_add x y
  map_smul' := by exact tensorMap_smul R K g

/-- The coefficient-linear algebraic map agrees with the primitive base-linear map. -/
theorem mapLinear_apply {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) (x : discreteExtendScalarsObj R K M) :
    mapLinear R K g x = mapRCLM R K g x := by
  let v : discreteExtendScalarsObj R K M → discreteExtendScalarsRObj R K M := fun z ↦ z
  let w : discreteExtendScalarsRObj R K N → discreteExtendScalarsObj R K N := fun z ↦ z
  let T : discreteExtendScalarsObj R K M → discreteExtendScalarsObj R K N :=
    fun z ↦ w (mapRCLM R K g (v z))
  have ht : @Eq (discreteExtendScalarsObj R K N)
      (rViewHomeomorph R K N (mapRCLM R K g ((rViewHomeomorph R K M).symm x)))
      (T x) := rfl
  exact (congrFun (tensorMap_rViewHomeomorph R K g) x).trans ht

/-- The coefficient-linear algebraic map intertwines the two carrier comparisons. -/
theorem mapLinear_rViewHomeomorph_apply
    {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) (x : discreteExtendScalarsRObj R K M) :
    mapLinear R K g (rViewHomeomorph R K M x) =
      rViewHomeomorph R K N (mapRCLM R K g x) := by
  exact (congrFun (tensorMap_rViewHomeomorph R K g) (rViewHomeomorph R K M x)).trans
    (congrArg (fun z : discreteExtendScalarsRObj R K M ↦
      rViewHomeomorph R K N (mapRCLM R K g z))
        ((rViewHomeomorph R K M).symm_apply_apply x))

/-- The coefficient-linear algebraic map respects the stored coefficient action. -/
theorem mapLinear_smul {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) (k : K) (x : discreteExtendScalarsObj R K M) :
    mapLinear R K g (k • x) = k • mapLinear R K g x :=
  (mapLinear R K g).map_smul k x

/-- The coefficient-linear tensor map inherits continuity from `mapRCLM`
through the identical topologies. Its target universe is independent. -/
noncomputable def mapCLM {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) : discreteExtendScalarsObj R K M →L[K]
      discreteExtendScalarsObj R K N where
  toLinearMap := mapLinear R K g
  cont := by
    refine (show Continuous (fun x : discreteExtendScalarsObj R K M ↦ mapLinear R K g x)
      from ?_)
    exact (((rViewHomeomorph R K N).continuous.comp (mapRCLM R K g).continuous).comp
      (rViewHomeomorph R K M).symm.continuous).congr
        (fun x : discreteExtendScalarsObj R K M ↦
          (congrFun (tensorMap_rViewHomeomorph R K g) x).symm)

/-- The coefficient-linear map agrees with the primitive `R`-map on every tensor. -/
theorem mapCLM_apply {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) (x : discreteExtendScalarsObj R K M) :
    mapCLM R K g x = mapRCLM R K g x := by
  exact mapLinear_apply R K g x

/-- The function of the coefficient-linear map is Mathlib's ordinary tensor map. -/
theorem mapCLM_tensorMap_apply {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) (x : discreteExtendScalarsObj R K M) :
    mapCLM R K g x = TensorProduct.map
      (LinearMap.id : coefficient R K →ₗ[R] coefficient R K) g.toLinearMap x := by
  let F : discreteExtendScalarsObj R K M → discreteExtendScalarsObj R K N :=
    TensorProduct.map (LinearMap.id : coefficient R K →ₗ[R] coefficient R K) g.toLinearMap
  exact (show @Eq (discreteExtendScalarsObj R K N) (mapCLM R K g x) (F x) from rfl)

/-- The coefficient-linear continuous map sends a pure tensor to its right-factor image. -/
@[simp]
theorem mapCLM_tmul {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) (c : K) (m : M) :
    mapCLM R K g (c ⊗ₜ[R] m) = c ⊗ₜ[R] g m := by
  have hp : @Eq (discreteExtendScalarsObj R K N)
      ((show discreteExtendScalarsObj R K M → discreteExtendScalarsObj R K N from
        TensorProduct.map (LinearMap.id : coefficient R K →ₗ[R] coefficient R K)
          g.toLinearMap) (c ⊗ₜ[R] m)) (c ⊗ₜ[R] g m) := by
    exact TensorProduct.map_tmul
      (LinearMap.id : coefficient R K →ₗ[R] coefficient R K) g.toLinearMap c m
  exact (mapCLM_tensorMap_apply R K g (c ⊗ₜ[R] m)).trans hp

/-- The continuous coefficient-linear map intertwines the two carrier comparisons. -/
theorem mapCLM_rViewHomeomorph_apply
    {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) (x : discreteExtendScalarsRObj R K M) :
    mapCLM R K g (rViewHomeomorph R K M x) =
      rViewHomeomorph R K N (mapRCLM R K g x) :=
  mapLinear_rViewHomeomorph_apply R K g x

/-- Scalar extension preserves identity continuous linear maps. -/
@[simp]
theorem mapCLM_id (M : TopModuleCat.{uM} R) :
    mapCLM R K (ContinuousLinearMap.id R M) =
      ContinuousLinearMap.id K (discreteExtendScalarsObj R K M) := by
  apply ContinuousLinearMap.ext
  intro x
  simpa only [← mapCLM_rViewHomeomorph_apply, Homeomorph.apply_symm_apply,
    ContinuousLinearMap.id_apply] using
      congrArg (rViewHomeomorph R K M)
        (DFunLike.congr_fun (mapRCLM_id R K M) ((rViewHomeomorph R K M).symm x))

/-- Scalar extension preserves composition, with independently leveled inputs. -/
theorem mapCLM_comp {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    {P : TopModuleCat.{uP} R} (g : M →L[R] N) (h : N →L[R] P) :
    mapCLM R K (h.comp g) = (mapCLM R K h).comp (mapCLM R K g) := by
  apply ContinuousLinearMap.ext
  intro x
  simpa only [ContinuousLinearMap.comp_apply, ← mapCLM_rViewHomeomorph_apply,
    Homeomorph.apply_symm_apply] using
      congrArg (rViewHomeomorph R K P)
        (DFunLike.congr_fun (mapRCLM_comp R K g h) ((rViewHomeomorph R K M).symm x))

omit [TopologicalSpace K] [DiscreteTopology K] in
/-- The unit is natural for the primitive `R`-linear tensor maps. -/
theorem unitContinuous_naturality {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) :
    (mapRCLM R K g).comp (unitContinuous R K M) = (unitContinuous R K N).comp g := by
  ext m
  simpa only [ContinuousLinearMap.comp_apply, unitContinuous_apply] using
    mapRCLM_tmul R K g 1 m

/-- Every pure tensor is the coefficient multiple of a unit vector in the coefficient view. -/
theorem tmul_eq_smul_unit (M : TopModuleCat.{uM} R) (c : K) (m : M) :
    @Eq (discreteExtendScalarsObj R K M) (c ⊗ₜ[R] m)
      (@SMul.smul K (discreteExtendScalarsObj R K M)
        (discreteExtendScalarsObj R K M).toModuleCat.isModule.toSMul c
        (rViewHomeomorph R K M (unitContinuous R K M m))) := by
  let p : K → M → discreteExtendScalarsObj R K M := fun a n ↦ a ⊗ₜ[R] n
  let pR : K → M → discreteExtendScalarsRObj R K M := fun a n ↦ a ⊗ₜ[R] n
  let s : K → discreteExtendScalarsObj R K M → discreteExtendScalarsObj R K M :=
    @SMul.smul K (discreteExtendScalarsObj R K M)
      (discreteExtendScalarsObj R K M).toModuleCat.isModule.toSMul
  have hr : @Eq (discreteExtendScalarsRObj R K M) (unitContinuous R K M m) (pR 1 m) :=
    unitContinuous_apply R K M m
  have hv : @Eq (discreteExtendScalarsObj R K M)
      (rViewHomeomorph R K M (pR 1 m)) (p 1 m) := rfl
  have hu : @Eq (discreteExtendScalarsObj R K M)
      (rViewHomeomorph R K M (unitContinuous R K M m)) (p 1 m) :=
    (congrArg (fun z : discreteExtendScalarsRObj R K M ↦ rViewHomeomorph R K M z) hr).trans hv
  have hm : @Eq (discreteExtendScalarsObj R K M) (p c m) (p (c * 1) m) :=
    congrArg (fun a : K ↦ p a m) (mul_one c).symm
  have hs : @Eq (discreteExtendScalarsObj R K M) (s c (p 1 m)) (p (c * 1) m) :=
    discreteExtendScalarsObj_smul_tmul R K M c 1 m
  exact hm.trans (hs.symm.trans (congrArg (s c) hu.symm))

/-- Outgoing coefficient-linear maps are determined by their values on the unit.
The target carrier universe is independent of the input universe. -/
@[ext]
theorem continuousLinearMap_ext (M : TopModuleCat.{uM} R) (N : TopModuleCat.{uN} K)
    {f g : discreteExtendScalarsObj R K M →L[K] N}
    (h : ∀ m : M, f (unitContinuous R K M m) = g (unitContinuous R K M m)) : f = g := by
  apply ContinuousLinearMap.ext
  intro x
  refine obj_inductionOn R K M
    (P := fun z : discreteExtendScalarsObj R K M ↦ @Eq N (f z) (g z)) x ?_ ?_
  · intro c m
    let u : discreteExtendScalarsObj R K M :=
      rViewHomeomorph R K M (unitContinuous R K M m)
    let s : K → discreteExtendScalarsObj R K M → discreteExtendScalarsObj R K M :=
      @SMul.smul K (discreteExtendScalarsObj R K M)
        (discreteExtendScalarsObj R K M).toModuleCat.isModule.toSMul
    let t : K → N → N := @SMul.smul K N N.toModuleCat.isModule.toSMul
    have hu : @Eq N (f u) (g u) := h m
    have hp : @Eq (discreteExtendScalarsObj R K M) (c ⊗ₜ[R] m) (s c u) :=
      tmul_eq_smul_unit R K M c m
    have hf : @Eq N (f (s c u)) (t c (f u)) := f.map_smul c u
    have hg : @Eq N (g (s c u)) (t c (g u)) := g.map_smul c u
    exact (congrArg (fun z : discreteExtendScalarsObj R K M ↦ f z) hp).trans
      (hf.trans ((congrArg (t c) hu).trans
        (hg.symm.trans (congrArg (fun z : discreteExtendScalarsObj R K M ↦ g z) hp.symm))))
  · intro x y hx hy
    exact (f.map_add x y).trans
      ((congrArg₂ (fun a b : N ↦
        @Add.add N N.toModuleCat.isAddCommGroup.toAdd a b) hx hy).trans (g.map_add x y).symm)

/-- Scalar extension of a categorical morphism; categorical Hom uses one carrier universe. -/
noncomputable def map {M N : TopModuleCat.{uM} R} (g : M ⟶ N) :
    discreteExtendScalarsObj R K M ⟶ discreteExtendScalarsObj R K N :=
  -- Use the stored coefficient objects, rather than reconstructing them from their carriers.
  ConcreteCategory.ofHom (C := TopModuleCat K) (X := discreteExtendScalarsObj R K M)
    (Y := discreteExtendScalarsObj R K N) (mapCLM R K g.hom)

private theorem map_hom {M N : TopModuleCat.{uM} R} (g : M ⟶ N) :
    (map R K g).hom = mapCLM R K g.hom := rfl

/-- Scalar extension of a categorical morphism has the same underlying tensor map. -/
@[simp]
theorem map_apply {M N : TopModuleCat.{uM} R} (g : M ⟶ N)
    (x : discreteExtendScalarsObj R K M) : map R K g x = mapCLM R K g.hom x := rfl

/-- Scalar extension of a categorical morphism sends a pure tensor to its image. -/
@[simp]
theorem map_tmul {M N : TopModuleCat.{uM} R} (g : M ⟶ N) (c : K) (m : M) :
    map R K g (c ⊗ₜ[R] m) = c ⊗ₜ[R] g m := mapCLM_tmul R K g.hom c m

/-- Scalar extension preserves categorical identity morphisms. -/
@[simp]
theorem map_id (M : TopModuleCat.{uM} R) : map R K (𝟙 M) = 𝟙 _ := by
  apply ConcreteCategory.ext
  simpa only [map_hom, hom_id] using mapCLM_id R K M

/-- Scalar extension preserves categorical composition. -/
theorem map_comp {M N P : TopModuleCat.{uM} R} (g : M ⟶ N) (h : N ⟶ P) :
    map R K (g ≫ h) = map R K g ≫ map R K h := by
  apply ConcreteCategory.ext
  simpa only [map_hom, hom_comp] using mapCLM_comp R K g.hom h.hom

end DiscreteExtendScalars

/-- Extension by a discrete coefficient algebra as a functor on topological modules. -/
noncomputable def discreteExtendScalars :
    TopModuleCat.{uM} R ⥤ TopModuleCat.{max uK uM} K where
  obj := discreteExtendScalarsObj R K
  map := DiscreteExtendScalars.map R K
  map_id := DiscreteExtendScalars.map_id R K
  map_comp := DiscreteExtendScalars.map_comp R K

/-- The scalar-extension functor has the canonical coefficient-linear object as its object map. -/
@[simp]
theorem discreteExtendScalars_obj (M : TopModuleCat.{uM} R) :
    (discreteExtendScalars R K).obj M = discreteExtendScalarsObj R K M := rfl

/-- The scalar-extension functor uses the canonical tensor map on each morphism. -/
@[simp]
theorem discreteExtendScalars_map {M N : TopModuleCat.{uM} R} (g : M ⟶ N) :
    (discreteExtendScalars R K).map g = DiscreteExtendScalars.map R K g := rfl

end Basic

section CommutativeCoefficient

variable (R : Type uR) (K : Type uK)
variable [CommRing R] [CommRing K] [Algebra R K] [TopologicalSpace R]
variable [TopologicalSpace K] [DiscreteTopology K]

namespace DiscreteExtendScalars

/-- The underlying coefficient module is canonically isomorphic to Mathlib's
algebraic extension of scalars for commutative `K`, with the identity pure-tensor comparison. -/
noncomputable def moduleCatComparisonIso (M : TopModuleCat.{uM} R) :
    (discreteExtendScalarsObj R K M).toModuleCat ≅
      (ModuleCat.extendScalars (algebraMap R K)).obj M.toModuleCat := by
  let C := (ModuleCat.restrictScalars (algebraMap R K)).obj (ModuleCat.of K K)
  let eR : coefficient R K ≃ₗ[R] C :=
    { toFun := fun c ↦ c
      invFun := fun c ↦ c
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        let E : coefficient R K → C := fun c ↦ c
        let s : R → coefficient R K → coefficient R K :=
          @SMul.smul R (coefficient R K) (coefficient R K).isModule.toSMul
        let t : R → C → C := @SMul.smul R C C.isModule.toSMul
        refine (show ∀ (r : R) (c : coefficient R K),
          @Eq C (E (s r c)) (t ((RingHom.id R) r) (E c)) from ?_)
        intro r c
        have hs : @Eq C (E (s r c)) (E (algebraMap R K r * c)) :=
          congrArg E (coefficient_stored_smul R K r c)
        have ht : @Eq C (t r (E c)) (E (algebraMap R K r * c)) :=
          restrictScalars_canonical_smul R K r (E c)
        have hi : @Eq C (t ((RingHom.id R) r) (E c)) (t r (E c)) :=
          congrArg (fun a : R ↦ t a (E c)) (show (RingHom.id R) r = r from rfl)
        exact hs.trans (ht.symm.trans hi.symm) }
  let tR := TensorProduct.congr eR (LinearEquiv.refl R M)
  let eK : (discreteExtendScalarsObj R K M).toModuleCat ≃ₗ[K]
      (ModuleCat.extendScalars (algebraMap R K)).obj M.toModuleCat :=
    { toFun := tR
      invFun := tR.symm
      left_inv := tR.left_inv
      right_inv := tR.right_inv
      map_add' := tR.map_add
      map_smul' := by
        let A := discreteExtendScalarsObj R K M
        let B := (ModuleCat.extendScalars (algebraMap R K)).obj M.toModuleCat
        let F : A → B := tR
        let s : K → A → A := @SMul.smul K A A.toModuleCat.isModule.toSMul
        let t : K → B → B := @SMul.smul K B B.isModule.toSMul
        let a : A → A → A := @Add.add A A.toModuleCat.isAddCommGroup.toAdd
        let b : B → B → B := @Add.add B B.isAddCommGroup.toAdd
        let p : K → M → A := fun c m ↦ c ⊗ₜ[R] m
        let q : K → M → B := fun c m ↦ c ⊗ₜ[R, algebraMap R K] m
        let v : A → @TensorProduct R
            (@CommRing.toCommSemiring R ‹CommRing R›) (coefficient R K) M
            (coefficient R K).isAddCommGroup.toAddCommMonoid
            M.toModuleCat.isAddCommGroup.toAddCommMonoid
            (coefficient R K).isModule M.toModuleCat.isModule := fun x ↦ x
        let w : @TensorProduct R
            (@CommRing.toCommSemiring R ‹CommRing R›) C M
            C.isAddCommGroup.toAddCommMonoid M.toModuleCat.isAddCommGroup.toAddCommMonoid
            C.isModule M.toModuleCat.isModule → B := fun x ↦ x
        refine (show ∀ (k : K) (x : A),
          @Eq B (F (s k x)) (t ((RingHom.id K) k) (F x)) from ?_)
        intro k x
        have ht (c : K) (m : M) : @Eq B (F (p c m)) (q c m) := by
          have hin : @Eq B (F (p c m))
              (w (tR ((show coefficient R K from c) ⊗ₜ[R] m))) := rfl
          have hout : @Eq B
              (w ((eR (show coefficient R K from c)) ⊗ₜ[R]
                (LinearEquiv.refl R M m))) (q c m) := rfl
          exact hin.trans
            ((congrArg w (TensorProduct.congr_tmul eR (LinearEquiv.refl R M)
              (show coefficient R K from c) m)).trans hout)
        have ha (x y : A) : @Eq B (F (a x y)) (b (F x) (F y)) := by
          have hin : @Eq B (F (a x y)) (w (tR (v x + v y))) := rfl
          have hout : @Eq B (w (tR (v x) + tR (v y))) (b (F x) (F y)) := rfl
          exact hin.trans ((congrArg w (tR.map_add (v x) (v y))).trans hout)
        have htp (c : K) (m : M) : @Eq B (t k (q c m)) (q (k * c) m) :=
          ModuleCat.ExtendScalars.smul_tmul (algebraMap R K)
            (M := M.toModuleCat) k c m
        have hsa (x y : A) : @Eq A (s k (a x y)) (a (s k x) (s k y)) :=
          @DistribMulAction.smul_add K A (inferInstance : Monoid K)
            A.toModuleCat.isAddCommGroup.toAddMonoid
            A.toModuleCat.isModule.toDistribMulAction k x y
        have hta (x y : B) : @Eq B (t k (b x y)) (b (t k x) (t k y)) :=
          @DistribMulAction.smul_add K B (inferInstance : Monoid K)
            B.isAddCommGroup.toAddMonoid B.isModule.toDistribMulAction k x y
        refine @Eq.trans B (F (s k x)) (t k (F x)) (t ((RingHom.id K) k) (F x)) ?_ ?_
        · refine obj_inductionOn R K M
            (P := fun z : A ↦ @Eq B (F (s k z)) (t k (F z))) x ?_ ?_
          · intro c m
            have hp : @Eq A (s k (p c m)) (p (k * c) m) :=
              discreteExtendScalarsObj_smul_tmul R K M k c m
            exact (congrArg F hp).trans
              ((ht (k * c) m).trans
                ((htp c m).symm.trans (congrArg (t k) (ht c m).symm)))
          · intro x y hx hy
            exact (congrArg F (hsa x y)).trans
              ((ha (s k x) (s k y)).trans
                ((congrArg₂ b hx hy).trans
                  ((hta (F x) (F y)).symm.trans (congrArg (t k) (ha x y).symm))))
        · exact congrArg (fun a : K ↦ t a (F x)) (show k = (RingHom.id K) k from rfl) }
  exact eK.toModuleIso

/-- The underlying-module comparison sends a tensor to the same pure tensor. -/
@[simp]
theorem moduleCatComparisonIso_hom_tmul (M : TopModuleCat.{uM} R) (c : K) (m : M) :
    (moduleCatComparisonIso R K M).hom (c ⊗ₜ[R] m) =
      c ⊗ₜ[R, algebraMap R K] m := by
  rfl

/-- The linear map of the underlying-module comparison has the same pure-tensor value. -/
@[simp]
theorem moduleCatComparisonIso_linear_tmul (M : TopModuleCat.{uM} R) (c : K) (m : M) :
    (moduleCatComparisonIso R K M).hom.hom (c ⊗ₜ[R] m) =
      c ⊗ₜ[R, algebraMap R K] m :=
  moduleCatComparisonIso_hom_tmul R K M c m

/-- The underlying-module comparison is natural in continuous input morphisms. -/
theorem moduleCatComparison_naturality {M N : TopModuleCat.{uM} R} (g : M ⟶ N) :
    ModuleCat.ofHom (map R K g).hom.toLinearMap ≫ (moduleCatComparisonIso R K N).hom =
      (moduleCatComparisonIso R K M).hom ≫
        (ModuleCat.extendScalars (algebraMap R K)).map
          (ModuleCat.ofHom g.hom.toLinearMap) := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
  let F : (discreteExtendScalarsObj R K M).toModuleCat →ₗ[K]
      (ModuleCat.extendScalars (algebraMap R K)).obj N.toModuleCat :=
    (moduleCatComparisonIso R K N).hom.hom.comp (map R K g).hom.toLinearMap
  let G : (discreteExtendScalarsObj R K M).toModuleCat →ₗ[K]
      (ModuleCat.extendScalars (algebraMap R K)).obj N.toModuleCat :=
    ((ModuleCat.extendScalars (algebraMap R K)).map
      (ModuleCat.ofHom g.hom.toLinearMap)).hom.comp (moduleCatComparisonIso R K M).hom.hom
  change F = G
  apply LinearMap.ext
  intro x
  refine obj_inductionOn R K M
    (P := fun z : discreteExtendScalarsObj R K M ↦ F z = G z) x ?_ ?_
  · intro c m
    let A := discreteExtendScalarsObj R K N
    let B := (ModuleCat.extendScalars (algebraMap R K)).obj M.toModuleCat
    let D := (ModuleCat.extendScalars (algebraMap R K)).obj N.toModuleCat
    let V : A → D := (moduleCatComparisonIso R K N).hom.hom
    let U : B → D := ((ModuleCat.extendScalars (algebraMap R K)).map
      (ModuleCat.ofHom g.hom.toLinearMap)).hom
    have hfin : @Eq D (F (c ⊗ₜ[R] m)) (V (mapCLM R K g.hom (c ⊗ₜ[R] m))) := rfl
    have hf : @Eq D (F (c ⊗ₜ[R] m)) (c ⊗ₜ[R, algebraMap R K] g.hom m) :=
      hfin.trans ((congrArg V (mapCLM_tmul R K g.hom c m)).trans
        (moduleCatComparisonIso_linear_tmul R K N c (g.hom m)))
    have hgin : @Eq D (G (c ⊗ₜ[R] m))
        (U ((moduleCatComparisonIso R K M).hom.hom (c ⊗ₜ[R] m))) := rfl
    have hc : @Eq B ((moduleCatComparisonIso R K M).hom.hom (c ⊗ₜ[R] m))
        (c ⊗ₜ[R, algebraMap R K] m) :=
      moduleCatComparisonIso_linear_tmul R K M c m
    have hm : @Eq D (U (c ⊗ₜ[R, algebraMap R K] m))
        (c ⊗ₜ[R, algebraMap R K] g.hom m) :=
      ModuleCat.ExtendScalars.map_tmul (algebraMap R K)
        (ModuleCat.ofHom g.hom.toLinearMap) c m
    have hg : @Eq D (G (c ⊗ₜ[R] m)) (c ⊗ₜ[R, algebraMap R K] g.hom m) :=
      hgin.trans ((congrArg U hc).trans hm)
    exact hf.trans hg.symm
  · intro x y hx hy
    exact (F.map_add x y).trans
      ((congrArg₂ (fun a b : (ModuleCat.extendScalars (algebraMap R K)).obj N.toModuleCat ↦
        @Add.add ((ModuleCat.extendScalars (algebraMap R K)).obj N.toModuleCat)
          ((ModuleCat.extendScalars (algebraMap R K)).obj N.toModuleCat).isAddCommGroup.toAdd
          a b) hx hy).trans (G.map_add x y).symm)

end DiscreteExtendScalars

end CommutativeCoefficient

section FiniteFieldSpecialization

/-- Finite-dimensional discrete-field specialization of the canonical scalar-extension object. -/
noncomputable def finiteExtendScalarsObj
    (R : Type uR) (K : Type uK) [Field R] [Field K] [Algebra R K]
    [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace K] [DiscreteTopology K]
    [FiniteDimensional R K] (M : TopModuleCat.{uM} R) : TopModuleCat.{max uK uM} K :=
  discreteExtendScalarsObj R K M

/-- The finite-field object is the specialization of extension by a discrete algebra. -/
theorem finiteExtendScalarsObj_eq_discreteExtendScalarsObj
    (R : Type uR) (K : Type uK) [Field R] [Field K] [Algebra R K]
    [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace K] [DiscreteTopology K]
    [FiniteDimensional R K] (M : TopModuleCat.{uM} R) :
    finiteExtendScalarsObj R K M = discreteExtendScalarsObj R K M := rfl

/-- Finite-dimensional discrete-field specialization of the scalar-extension functor. -/
noncomputable def finiteExtendScalars
    (R : Type uR) (K : Type uK) [Field R] [Field K] [Algebra R K]
    [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace K] [DiscreteTopology K]
    [FiniteDimensional R K] : TopModuleCat.{uM} R ⥤ TopModuleCat.{max uK uM} K :=
  discreteExtendScalars R K

/-- The finite-field functor is the specialization of extension by a discrete algebra. -/
theorem finiteExtendScalars_eq_discreteExtendScalars
    (R : Type uR) (K : Type uK) [Field R] [Field K] [Algebra R K]
    [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace K] [DiscreteTopology K]
    [FiniteDimensional R K] :
    (finiteExtendScalars R K : TopModuleCat.{uM} R ⥤ TopModuleCat.{max uK uM} K) =
      discreteExtendScalars R K := rfl

namespace FiniteExtendScalars

/-- The base-linear view of finite-dimensional discrete-field scalar extension. -/
noncomputable def baseObj
    (R : Type uR) (K : Type uK) [Field R] [Field K] [Algebra R K]
    [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace K] [DiscreteTopology K]
    [FiniteDimensional R K] (M : TopModuleCat.{uM} R) : TopModuleCat.{max uK uM} R :=
  discreteExtendScalarsRObj R K M

/-- The finite-field unit uses the base-linear view, separately from the
coefficient-linear object. -/
noncomputable def unitContinuous
    (R : Type uR) (K : Type uK) [Field R] [Field K] [Algebra R K]
    [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace K] [DiscreteTopology K]
    [FiniteDimensional R K] (M : TopModuleCat.{uM} R) : M →L[R] baseObj R K M :=
  DiscreteExtendScalars.unitContinuous R K M

/-- The finite-field unit is the generator at `1`. -/
@[simp]
theorem unitContinuous_apply
    (R : Type uR) (K : Type uK) [Field R] [Field K] [Algebra R K]
    [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace K] [DiscreteTopology K]
    [FiniteDimensional R K] (M : TopModuleCat.{uM} R) (m : M) :
    unitContinuous R K M m = (1 : K) ⊗ₜ[R] m := rfl

/-- The finite-field unit specializes the unit for discrete coefficient algebras. -/
theorem unitContinuous_eq_discreteUnit
    (R : Type uR) (K : Type uK) [Field R] [Field K] [Algebra R K]
    [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace K] [DiscreteTopology K]
    [FiniteDimensional R K] (M : TopModuleCat.{uM} R) :
    unitContinuous R K M = DiscreteExtendScalars.unitContinuous R K M := rfl

end FiniteExtendScalars

end FiniteFieldSpecialization

end TopModuleCat
