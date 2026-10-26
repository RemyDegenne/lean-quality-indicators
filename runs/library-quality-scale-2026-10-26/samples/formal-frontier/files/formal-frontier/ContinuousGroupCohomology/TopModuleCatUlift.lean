/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Formal Frontier Agents
Original topological development: Beacon
The universe-lift functor and fully-faithful construction adapt
Mathlib/Algebra/Category/ModuleCat/Ulift.lean at
e37d88a26f3791ed5a93daa1f949af1021b8d103.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic

/-!
# Universe lifts of topological modules

This file provides the universe-raising functor for `TopModuleCat`, parallel to
`ModuleCat.uliftFunctor`. Its action on a morphism is conjugation by the
canonical continuous linear equivalences between a type and its `ULift`.
-/

set_option warningAsError true

@[expose] public section

universe v' v u

open CategoryTheory

namespace ULift

/-- Raising the universe of a topological additive group preserves its
topological additive group structure. -/
instance instIsTopologicalAddGroupOfIsTopologicalAddGroup
    {M : Type v} [AddGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] :
    IsTopologicalAddGroup (ULift.{v'} M) where

variable {R : Type u} {M : Type v} [Semiring R] [TopologicalSpace R]
  [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousSMul R M]

/-- A scalar action remains continuous after raising the universe of the
acted-on type. -/
instance instContinuousSMulOfContinuousSMul : ContinuousSMul R (ULift.{v'} M) where
  continuous_smul :=
    (ContinuousLinearEquiv.ulift (R₁ := R) (M₁ := M)).symm.continuous.comp
      (continuous_fst.smul
        ((ContinuousLinearEquiv.ulift (R₁ := R) (M₁ := M)).continuous.comp continuous_snd))

end ULift

namespace TopModuleCat

variable (R : Type u) [Ring R] [TopologicalSpace R]

/-- Raise the universe of a topological `R`-module. -/
@[simps obj map, pp_with_univ]
def uliftFunctor : TopModuleCat.{v} R ⥤ TopModuleCat.{max v v'} R where
  obj X := TopModuleCat.of R (ULift.{v'} X)
  map {X Y} f := TopModuleCat.ofHom
    ((ContinuousLinearEquiv.ulift (R₁ := R) (M₁ := Y)).symm.toContinuousLinearMap.comp
      (f.hom.comp
        (ContinuousLinearEquiv.ulift (R₁ := R) (M₁ := X)).toContinuousLinearMap))
  map_id X := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

/-- The universe-raising functor on topological modules is fully faithful. -/
def fullyFaithfulUliftFunctor : (uliftFunctor.{v', v} R).FullyFaithful where
  preimage {X Y} f := TopModuleCat.ofHom
    ((ContinuousLinearEquiv.ulift (R₁ := R) (M₁ := Y)).toContinuousLinearMap.comp
      (f.hom.comp
        (ContinuousLinearEquiv.ulift (R₁ := R) (M₁ := X)).symm.toContinuousLinearMap))

instance : (uliftFunctor.{v', v} R).Full := (fullyFaithfulUliftFunctor R).full

instance : (uliftFunctor.{v', v} R).Faithful := (fullyFaithfulUliftFunctor R).faithful

instance : (uliftFunctor.{v', v} R).Additive where

/-- The original topological module is canonically continuously linearly
equivalent to the carrier of its universe lift. -/
def uliftFunctorObjEquiv (X : TopModuleCat.{v} R) :
    X ≃L[R] (uliftFunctor.{v', v} R).obj X :=
  (ContinuousLinearEquiv.ulift (R₁ := R) (M₁ := X)).symm

@[simp]
lemma uliftFunctorObjEquiv_apply (X : TopModuleCat.{v} R) (x : X) :
    uliftFunctorObjEquiv.{v', v} R X x = ULift.up x :=
  rfl

@[simp]
lemma uliftFunctorObjEquiv_symm_apply (X : TopModuleCat.{v} R)
    (x : (uliftFunctor.{v', v} R).obj X) :
    (uliftFunctorObjEquiv.{v', v} R X).symm x = x.down :=
  rfl

@[simp]
lemma uliftFunctorObjEquiv_naturality {X Y : TopModuleCat.{v} R} (f : X ⟶ Y) (x : X) :
    uliftFunctorObjEquiv R Y (f.hom x) =
      ((uliftFunctor.{v', v} R).map f).hom (uliftFunctorObjEquiv R X x) :=
  rfl

@[simp]
lemma uliftFunctorObjEquiv_symm_naturality {X Y : TopModuleCat.{v} R} (f : X ⟶ Y)
    (x : (uliftFunctor.{v', v} R).obj X) :
    f.hom ((uliftFunctorObjEquiv R X).symm x) =
      (uliftFunctorObjEquiv R Y).symm
        (((uliftFunctor.{v', v} R).map f).hom x) :=
  rfl

/-- In one fixed object universe, the identity functor on topological modules is
naturally isomorphic to universe lifting. -/
noncomputable def uliftFunctorIsoSameUniverse :
    Functor.id (TopModuleCat.{v} R) ≅ uliftFunctor.{v, v} R :=
  NatIso.ofComponents
    (fun X => TopModuleCat.ofIso (uliftFunctorObjEquiv.{v, v} R X))
    (fun f => by ext x; rfl)

/-- Same-universe lifting of topological modules is essentially surjective. -/
instance instEssSurjUliftFunctorSameUniverse :
    (uliftFunctor.{v, v} R).EssSurj :=
  Functor.essSurj_of_iso (uliftFunctorIsoSameUniverse.{v} R)

/-- Same-universe lifting is an equivalence of the category of topological
modules with itself. -/
instance instIsEquivalenceUliftFunctorSameUniverse :
    (uliftFunctor.{v, v} R).IsEquivalence where

end TopModuleCat

namespace TopModuleCat

variable (R : Type u) [CommRing R] [TopologicalSpace R]

instance : (uliftFunctor.{v', v} R).Linear R where

end TopModuleCat
