/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Restriction of scalars with unchanged topology

A continuous ring homomorphism `φ : R →+* S` restricts a topological `S`-module
without changing its carrier, additive group or topology. Its `R`-action is
`r • x = φ r • x`. The algebraic component is Mathlib's
`ModuleCat.restrictScalars φ`, rather than a second module construction.

`TopModuleCat.restrictScalarsObj` names the object, and
`TopModuleCat.restrictScalarsCLM` restricts continuous linear maps between
objects with independently leveled carriers. `TopModuleCat.restrictScalars`
packages the same operation as a functor in a fixed carrier universe.
Both scalar actions are passed explicitly to Mathlib's continuous-linear
restriction, so restriction along a nonidentity endomorphism of one ring does
not require competing scalar instances on the original carrier.

For arbitrary semirings with supplied topologies and continuous multiplication
on `S`, continuity of `φ` is equivalent to joint continuity of its restricted
regular action: evaluating that action at `1` recovers `φ`. For rings, this
tests restriction of every object whenever the regular module `S` is itself
topological. The algebra-map multiplication formula agrees with the Algebra
scalar action, so the criterion recovers Mathlib's `continuous_algebraMap_iff_smul`
without any discreteness or finiteness assumption. This is separate from
continuity of a particular linear map on a scalar-extension object.

Restriction preserves continuous-linear identities and composition, commutes
with forgetting to modules and topological spaces, and has natural identity
and composition comparisons.

## Limitations

This module does not assert an extension/restriction adjunction or a finite-free
continuous Hom equivalence.

## References

This generalizes the same-topology restriction object and continuous-map
construction in the scalar-extension formalization of
[Continuous Group Cohomology](https://github.com/FormalFrontier/continuous-group-cohomology),
by Formal Frontier Agents, including Beacon's original development.
The algebraic objects and comparison isomorphisms reuse Jujian Zhang's Mathlib
`Algebra.Category.ModuleCat.ChangeOfRings`. Continuous maps reuse Sébastien
Gouëzel and Yury Kudryashov's `ContinuousLinearMap.restrictScalars`.
Topological bundles and the surrounding coinduction API are due to Richard Hill
and Andrew Yang in Mathlib's `Algebra.Category.ModuleCat.Topology.Basic`.
The regular-action continuity criterion generalizes Mathlib's
`continuous_algebraMap_iff_smul` in `Topology.Algebra.Algebra`, whose contributors
are Kim Morrison, Antoine Chambert-Loir and María Inés de Frutos-Fernández.
The agreement of the action formulas uses Mathlib's `Algebra.smul_def`.
Rewriting the criterion's right-hand side by `algebraMap_mulAction_eq_smul` at
`φ = algebraMap R S` recovers that Mathlib equivalence throughout its
commutative-semiring scope, for arbitrary supplied topologies.
-/

@[expose] public section

universe uR uS uT uM uN uP uY

open CategoryTheory

namespace TopModuleCat

section Restriction

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable [TopologicalSpace R] [TopologicalSpace S]
variable (φ : R →+* S) (hφ : Continuous φ)

/-- Restrict a topological module along a continuous ring homomorphism,
retaining its topology and using Mathlib's algebraic restriction object.
The bundle is reducible so its unchanged carrier is available to instance search. -/
noncomputable abbrev restrictScalarsObj (M : TopModuleCat.{uM} S) : TopModuleCat.{uM} R :=
  let A := (ModuleCat.restrictScalars φ).obj M.toModuleCat
  letI : AddCommGroup M := A.isAddCommGroup
  letI : Module R M := A.isModule
  letI : TopologicalSpace M := M.topologicalSpace
  letI : ContinuousSMul R M :=
    @ContinuousSMul.mk R M A.isModule.toSMul _ M.topologicalSpace (by
      change Continuous (fun p : R × M ↦ φ p.1 • p.2)
      exact continuous_smul.comp ((hφ.comp continuous_fst).prodMk continuous_snd))
  -- `ModuleCat.of` retains exactly A's fields while exposing the original carrier.
  @TopModuleCat.mk R _ _ (@ModuleCat.of R _ M A.isAddCommGroup A.isModule)
    M.topologicalSpace M.isTopologicalAddGroup inferInstance

/-- The carrier of restriction is the original carrier. -/
@[simp]
theorem coe_restrictScalarsObj (M : TopModuleCat.{uM} S) :
    (restrictScalarsObj φ hφ M : Type uM) = M := rfl

/-- The underlying module is precisely Mathlib's restriction of scalars. -/
@[simp]
theorem restrictScalarsObj_toModuleCat (M : TopModuleCat.{uM} S) :
    (restrictScalarsObj φ hφ M).toModuleCat =
      (ModuleCat.restrictScalars φ).obj M.toModuleCat := rfl

/-- Restriction retains the supplied topology, not a newly coinduced topology. -/
@[simp]
theorem restrictScalarsObj_topologicalSpace (M : TopModuleCat.{uM} S) :
    (restrictScalarsObj φ hφ M).topologicalSpace = M.topologicalSpace := rfl

/-- Restriction retains addition on the carrier. -/
@[simp]
theorem restrictScalarsObj_add (M : TopModuleCat.{uM} S) (x y : M) :
    (show restrictScalarsObj φ hφ M from x) + (show restrictScalarsObj φ hφ M from y) =
      (show restrictScalarsObj φ hφ M from x + y) := rfl

/-- The restricted action is the original action after applying the ring homomorphism.
The two bundled scalar views remain explicit even when `R = S`. -/
@[simp]
theorem restrictScalarsObj_smul (M : TopModuleCat.{uM} S) (r : R) (x : M) :
    r • (show restrictScalarsObj φ hφ M from x) =
      (show restrictScalarsObj φ hφ M from φ r • x) := rfl

/-- Unchanged topology preserves and reflects continuity of every carrier function. -/
theorem continuous_restrictScalarsObj_iff (M : TopModuleCat.{uM} S)
    {Y : Type uY} [TopologicalSpace Y] (f : M → Y) :
    Continuous (fun x : restrictScalarsObj φ hφ M ↦ f x) ↔ Continuous f := Iff.rfl

/-- Restrict a continuous `S`-linear map to the two canonical `R`-views.
The source and target carrier universes are independent. Both original and
restricted module structures are supplied explicitly to Mathlib's restriction
of continuous linear maps, including when the scalar rings coincide. -/
noncomputable def restrictScalarsCLM {M : TopModuleCat.{uM} S} {N : TopModuleCat.{uN} S}
    (f : M →L[S] N) : restrictScalarsObj φ hφ M →L[R] restrictScalarsObj φ hφ N :=
  @ContinuousLinearMap.restrictScalars S M N R
    inferInstance inferInstance inferInstance
    M.toModuleCat.isModule (restrictScalarsObj φ hφ M).toModuleCat.isModule M.topologicalSpace
    inferInstance N.toModuleCat.isModule
    (restrictScalarsObj φ hφ N).toModuleCat.isModule N.topologicalSpace
    (@LinearMap.CompatibleSMul.mk M N inferInstance inferInstance R S inferInstance
      (restrictScalarsObj φ hφ M).toModuleCat.isModule.toSMul M.toModuleCat.isModule
      (restrictScalarsObj φ hφ N).toModuleCat.isModule.toSMul N.toModuleCat.isModule
      (fun g r x ↦ g.map_smul (φ r) x)) f

/-- Restriction of a continuous linear map leaves its function unchanged. -/
@[simp]
theorem restrictScalarsCLM_apply {M : TopModuleCat.{uM} S} {N : TopModuleCat.{uN} S}
    (f : M →L[S] N) (x : M) : restrictScalarsCLM φ hφ f x = f x := rfl

/-- Function-level characteristic formula for restricted continuous linear maps. -/
theorem coe_restrictScalarsCLM {M : TopModuleCat.{uM} S} {N : TopModuleCat.{uN} S}
    (f : M →L[S] N) :
    (restrictScalarsCLM φ hφ f : restrictScalarsObj φ hφ M → restrictScalarsObj φ hφ N) =
      (fun x ↦ f x) := rfl

/-- In a common carrier universe, the underlying linear map is Mathlib's
algebraic restriction map. -/
theorem restrictScalarsCLM_toLinearMap {M N : TopModuleCat.{uM} S} (f : M →L[S] N) :
    (restrictScalarsCLM φ hφ f).toLinearMap =
      ((ModuleCat.restrictScalars φ).map
        (ModuleCat.ofHom (X := M) (Y := N) f.toLinearMap)).hom := by
  ext x
  rfl

/-- Restriction preserves the identity continuous linear map. -/
@[simp]
theorem restrictScalarsCLM_id (M : TopModuleCat.{uM} S) :
    restrictScalarsCLM φ hφ (ContinuousLinearMap.id S M) =
      ContinuousLinearMap.id R (restrictScalarsObj φ hφ M) := by
  ext x
  rfl

/-- Restriction preserves composition, with three independent carrier universes. -/
@[simp]
theorem restrictScalarsCLM_comp {M : TopModuleCat.{uM} S} {N : TopModuleCat.{uN} S}
    {P : TopModuleCat.{uP} S} (f : M →L[S] N) (g : N →L[S] P) :
    restrictScalarsCLM φ hφ (g.comp f) =
      (restrictScalarsCLM φ hφ g).comp (restrictScalarsCLM φ hφ f) := by
  ext x
  rfl

/-- Restriction of scalars as a functor, retaining the topology of each object.
Categorical morphisms have a common carrier universe; `restrictScalarsCLM`
provides the independently leveled continuous-linear interface. -/
noncomputable def restrictScalars : TopModuleCat.{uM} S ⥤ TopModuleCat.{uM} R where
  obj := restrictScalarsObj φ hφ
  map {M N} f := ofHom (X := restrictScalarsObj φ hφ M) (Y := restrictScalarsObj φ hφ N)
    (restrictScalarsCLM φ hφ f.hom)
  map_id M := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

/-- The functor's object is the named same-topology restriction object. -/
@[simp]
theorem restrictScalars_obj (M : TopModuleCat.{uM} S) :
    (restrictScalars φ hφ).obj M = restrictScalarsObj φ hφ M := rfl

/-- The functor's morphism is the named continuous-linear restriction map. -/
@[simp]
theorem restrictScalars_map_hom {M N : TopModuleCat.{uM} S} (f : M ⟶ N) :
    ((restrictScalars φ hφ).map f).hom = restrictScalarsCLM φ hφ f.hom := rfl

/-- A restricted categorical morphism retains its original values. -/
@[simp]
theorem restrictScalars_map_apply {M N : TopModuleCat.{uM} S} (f : M ⟶ N) (x : M) :
    (restrictScalars φ hφ).map f x = f x := rfl

/-- The restriction functor preserves identity morphisms. -/
@[simp]
theorem restrictScalars_map_id (M : TopModuleCat.{uM} S) :
    (restrictScalars φ hφ).map (𝟙 M) = 𝟙 ((restrictScalars φ hφ).obj M) :=
  (restrictScalars φ hφ).map_id M

/-- The restriction functor preserves composition of morphisms. -/
@[simp]
theorem restrictScalars_map_comp {M N P : TopModuleCat.{uM} S}
    (f : M ⟶ N) (g : N ⟶ P) :
    (restrictScalars φ hφ).map (f ≫ g) =
      (restrictScalars φ hφ).map f ≫ (restrictScalars φ hφ).map g :=
  (restrictScalars φ hφ).map_comp f g

/-- Forgetting topology commutes with restriction, using Mathlib's
`ModuleCat.restrictScalars` on both objects and maps. -/
theorem restrictScalars_comp_forgetModuleCat :
    (restrictScalars φ hφ : TopModuleCat.{uM} S ⥤ TopModuleCat.{uM} R) ⋙
        forget₂ (TopModuleCat.{uM} R) (ModuleCat.{uM} R) =
      forget₂ (TopModuleCat.{uM} S) (ModuleCat.{uM} S) ⋙ ModuleCat.restrictScalars φ := by
  refine Functor.hext (fun M ↦ rfl) ?_
  intro M N f
  apply heq_of_eq
  apply ModuleCat.hom_ext
  exact restrictScalarsCLM_toLinearMap φ hφ f.hom

/-- Forgetting the scalar action leaves the same topological-space functor. -/
theorem restrictScalars_comp_forgetTopCat :
    (restrictScalars φ hφ : TopModuleCat.{uM} S ⥤ TopModuleCat.{uM} R) ⋙
        forget₂ (TopModuleCat.{uM} R) TopCat.{uM} =
      forget₂ (TopModuleCat.{uM} S) TopCat.{uM} := by
  refine Functor.hext (fun M ↦ rfl) ?_
  intro M N f
  apply heq_of_eq
  ext x
  rfl

end Restriction

section Identity

variable {R : Type uR} [Ring R] [TopologicalSpace R]

/-- Restriction along the identity is isomorphic to the original object,
using Mathlib's algebraic identity comparison with unchanged topology. -/
noncomputable def restrictScalarsIdIso (M : TopModuleCat.{uM} R) :
    restrictScalarsObj (RingHom.id R) continuous_id M ≅ M :=
  ofIso
    { __ := ((ModuleCat.restrictScalarsId R).app M.toModuleCat).toLinearEquiv
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }

/-- The identity comparison is the identity on carrier elements. -/
@[simp]
theorem restrictScalarsIdIso_hom_apply (M : TopModuleCat.{uM} R) (x : M) :
    (restrictScalarsIdIso M).hom x = x := rfl

/-- The inverse identity comparison is the identity on carrier elements. -/
@[simp]
theorem restrictScalarsIdIso_inv_apply (M : TopModuleCat.{uM} R) (x : M) :
    (restrictScalarsIdIso M).inv x = x := rfl

/-- Restriction along the identity ring homomorphism is naturally isomorphic
to the identity functor. -/
noncomputable def restrictScalarsId :
    (restrictScalars (RingHom.id R) continuous_id : TopModuleCat.{uM} R ⥤ TopModuleCat.{uM} R) ≅
      𝟭 (TopModuleCat.{uM} R) :=
  NatIso.ofComponents restrictScalarsIdIso (by
    intro M N f
    ext x
    rfl)

/-- The identity natural comparison has the named objectwise component. -/
@[simp]
theorem restrictScalarsId_hom_app (M : TopModuleCat.{uM} R) :
    (restrictScalarsId (R := R)).hom.app M = (restrictScalarsIdIso M).hom := rfl

/-- The inverse identity natural comparison has the named objectwise component. -/
@[simp]
theorem restrictScalarsId_inv_app (M : TopModuleCat.{uM} R) :
    (restrictScalarsId (R := R)).inv.app M = (restrictScalarsIdIso M).inv := rfl

/-- The identity natural comparison retains every carrier element. -/
@[simp]
theorem restrictScalarsId_hom_app_apply (M : TopModuleCat.{uM} R) (x : M) :
    (restrictScalarsId (R := R)).hom.app M x = x := rfl

/-- The inverse identity natural comparison retains every carrier element. -/
@[simp]
theorem restrictScalarsId_inv_app_apply (M : TopModuleCat.{uM} R) (x : M) :
    (restrictScalarsId (R := R)).inv.app M x = x := rfl

end Identity

section Composition

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]
variable [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace T]
variable (φ : R →+* S) (ψ : S →+* T) (hφ : Continuous φ) (hψ : Continuous ψ)

/-- Restriction along a composite is isomorphic to successive restriction.
The algebraic comparison is Mathlib's, and both carrier functions are identities. -/
noncomputable def restrictScalarsCompIso (M : TopModuleCat.{uM} T) :
    restrictScalarsObj (ψ.comp φ) (hψ.comp hφ) M ≅
      restrictScalarsObj φ hφ (restrictScalarsObj ψ hψ M) :=
  ofIso
    { __ := ((ModuleCat.restrictScalarsComp φ ψ).app M.toModuleCat).toLinearEquiv
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }

/-- The composition comparison is the identity on the unchanged carrier. -/
@[simp]
theorem restrictScalarsCompIso_hom_apply (M : TopModuleCat.{uM} T) (x : M) :
    (restrictScalarsCompIso φ ψ hφ hψ M).hom x = x := rfl

/-- The inverse composition comparison is the identity on the unchanged carrier. -/
@[simp]
theorem restrictScalarsCompIso_inv_apply (M : TopModuleCat.{uM} T) (x : M) :
    (restrictScalarsCompIso φ ψ hφ hψ M).inv x = x := rfl

/-- Restriction along a composite is naturally isomorphic to the composite
of the two restriction functors, in the contravariant scalar order. -/
noncomputable def restrictScalarsComp :
    (restrictScalars (ψ.comp φ) (hψ.comp hφ) : TopModuleCat.{uM} T ⥤ TopModuleCat.{uM} R) ≅
      restrictScalars ψ hψ ⋙ restrictScalars φ hφ :=
  NatIso.ofComponents (restrictScalarsCompIso φ ψ hφ hψ) (by
    intro M N f
    ext x
    rfl)

/-- The composition natural comparison has the named objectwise component. -/
@[simp]
theorem restrictScalarsComp_hom_app (M : TopModuleCat.{uM} T) :
    (restrictScalarsComp φ ψ hφ hψ).hom.app M =
      (restrictScalarsCompIso φ ψ hφ hψ M).hom := rfl

/-- The inverse composition natural comparison has the named objectwise component. -/
@[simp]
theorem restrictScalarsComp_inv_app (M : TopModuleCat.{uM} T) :
    (restrictScalarsComp φ ψ hφ hψ).inv.app M =
      (restrictScalarsCompIso φ ψ hφ hψ M).inv := rfl

/-- The composition natural comparison retains every carrier element. -/
@[simp]
theorem restrictScalarsComp_hom_app_apply (M : TopModuleCat.{uM} T) (x : M) :
    (restrictScalarsComp φ ψ hφ hψ).hom.app M x = x := rfl

/-- The inverse composition natural comparison retains every carrier element. -/
@[simp]
theorem restrictScalarsComp_inv_app_apply (M : TopModuleCat.{uM} T) (x : M) :
    (restrictScalarsComp φ ψ hφ hψ).inv.app M x = x := rfl

end Composition

section Continuity

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
variable [TopologicalSpace R] [TopologicalSpace S]

/-- For the regular module of a semiring with continuous multiplication,
continuity of a semiring homomorphism is equivalent to joint continuity of its
restricted action. Evaluating the action at `1` gives the necessary direction;
no topological-semiring structure on the source is required. This generalizes
Mathlib's `continuous_algebraMap_iff_smul` from algebra maps to arbitrary
semiring homomorphisms. -/
theorem continuous_ringHom_iff_continuous_mulAction [ContinuousMul S] (φ : R →+* S) :
    Continuous φ ↔ Continuous (fun p : R × S ↦ φ p.1 * p.2) := by
  constructor
  · intro hφ
    exact (hφ.comp continuous_fst).mul continuous_snd
  · intro h
    -- Evaluation at 1 recovers the scalar map from the regular action.
    have hEval :=
      h.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : R ↦ (1 : S))))
    exact hEval.congr (fun r ↦ mul_one (φ r))

end Continuity

section Algebra

variable {R : Type uR} {S : Type uS} [CommSemiring R] [Semiring S] [Algebra R S]

/-- Multiplication through the algebra map is the Algebra scalar action,
as an equality of functions. This identifies the regular-action formula in
`continuous_ringHom_iff_continuous_mulAction` with the scalar-action formula in
Mathlib's `continuous_algebraMap_iff_smul` for any supplied topologies. -/
theorem algebraMap_mulAction_eq_smul :
    (fun p : R × S ↦ algebraMap R S p.1 * p.2) = (fun p : R × S ↦ p.1 • p.2) := by
  funext p
  exact (Algebra.smul_def p.1 p.2).symm

end Algebra

end TopModuleCat
