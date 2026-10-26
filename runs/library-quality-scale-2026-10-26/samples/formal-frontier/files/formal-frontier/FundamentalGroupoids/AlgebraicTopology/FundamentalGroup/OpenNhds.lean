/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.FundamentalGroup
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.Topology.Category.TopCat.OpenNhds

/-!
# Fundamental groups of open neighborhoods

The fundamental groups of the open neighborhoods of a point, based at that common
point, form a functor to groups. The inclusions into the ambient space give a
cocone with vertex its fundamental group. These constructions require neither
connectedness nor a covering hypothesis.

For a family `U : I → TopologicalSpace.OpenNhds x`, precomposition with
`CategoryTheory.inducedFunctor U` gives the diagram indexed by the induced
category on `I`. Its inclusion cocone is obtained from
`FundamentalGroup.openNhdsCocone x` using `CategoryTheory.Limits.Cocone.whisker`.
The universe of `I` is independent of the universe of the ambient space.

## References

* Mathlib's `Mathlib.Topology.Category.TopCat.OpenNhds`, by Kim Morrison,
  supplies the category of open neighborhoods.
* Mathlib's `Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup`,
  by Mark Lavrentyev, supplies the fundamental groups and induced based maps.
* `FundamentalGroupoids.FundamentalGroup` supplies the identity and composition
  laws for the induced homomorphisms.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace FundamentalGroup

variable {X : Type u} [TopologicalSpace X]

/-- The functor assigning to each open neighborhood of `x` its fundamental group
based at `x`, and to each inclusion the induced homomorphism. -/
def openNhdsFunctor (x : X) :
    OpenNhds (X := TopCat.of X) x ⥤ GrpCat.{u} where
  obj U := GrpCat.of (FundamentalGroup U.val (⟨x, U.property⟩ : U.val))
  -- Subtype inclusions preserve the common point definitionally.
  map {U V} i := GrpCat.ofHom
    (map (ContinuousMap.inclusion
      (s := (U.val : Set X)) (t := (V.val : Set X)) i.le)
      (⟨x, U.property⟩ : U.val))
  map_id U := by
    apply GrpCat.hom_ext
    change map (ContinuousMap.id U.val) (⟨x, U.property⟩ : U.val) =
      MonoidHom.id (FundamentalGroup U.val (⟨x, U.property⟩ : U.val))
    exact map_id (⟨x, U.property⟩ : U.val)
  map_comp {U V W} i j := by
    apply GrpCat.hom_ext
    change map
        ((ContinuousMap.inclusion (s := (V.val : Set X)) (t := (W.val : Set X)) j.le).comp
          (ContinuousMap.inclusion (s := (U.val : Set X)) (t := (V.val : Set X)) i.le))
        (⟨x, U.property⟩ : U.val) =
      (map (ContinuousMap.inclusion
        (s := (V.val : Set X)) (t := (W.val : Set X)) j.le)
        (⟨x, V.property⟩ : V.val)).comp
      (map (ContinuousMap.inclusion
        (s := (U.val : Set X)) (t := (V.val : Set X)) i.le)
        (⟨x, U.property⟩ : U.val))
    exact map_comp
      (ContinuousMap.inclusion (s := (V.val : Set X)) (t := (W.val : Set X)) j.le)
      (ContinuousMap.inclusion (s := (U.val : Set X)) (t := (V.val : Set X)) i.le)
      (⟨x, U.property⟩ : U.val)

/-- The group assigned to an open neighborhood is its fundamental group at the common point. -/
@[simp]
theorem openNhdsFunctor_obj (x : X) (U : OpenNhds (X := TopCat.of X) x) :
    (openNhdsFunctor x).obj U =
      GrpCat.of (FundamentalGroup U.val (⟨x, U.property⟩ : U.val)) := rfl

/-- The carrier of the group assigned to an open neighborhood is its fundamental group. -/
theorem openNhdsFunctor_obj_coe (x : X) (U : OpenNhds (X := TopCat.of X) x) :
    ((openNhdsFunctor x).obj U : Type u) =
      FundamentalGroup U.val (⟨x, U.property⟩ : U.val) := rfl

/-- An inclusion of neighborhoods is sent to its induced based homomorphism. -/
theorem openNhdsFunctor_map (x : X) {U V : OpenNhds (X := TopCat.of X) x}
    (i : U ⟶ V) :
    (openNhdsFunctor x).map i = GrpCat.ofHom
      (map (ContinuousMap.inclusion
        (s := (U.val : Set X)) (t := (V.val : Set X)) i.le)
        (⟨x, U.property⟩ : U.val)) := rfl

/-- The underlying homomorphism of a neighborhood inclusion is induced by subtype inclusion. -/
@[simp]
theorem openNhdsFunctor_map_hom (x : X) {U V : OpenNhds (X := TopCat.of X) x}
    (i : U ⟶ V) :
    ((openNhdsFunctor x).map i).hom =
      map (ContinuousMap.inclusion
        (s := (U.val : Set X)) (t := (V.val : Set X)) i.le)
        (⟨x, U.property⟩ : U.val) := rfl

/-- A neighborhood inclusion acts on loop classes by mapping their representative paths. -/
theorem openNhdsFunctor_map_hom_apply (x : X)
    {U V : OpenNhds (X := TopCat.of X) x} (i : U ⟶ V)
    (γ : FundamentalGroup U.val (⟨x, U.property⟩ : U.val)) :
    ((openNhdsFunctor x).map i).hom γ =
      Path.Homotopic.Quotient.map γ (ContinuousMap.inclusion
        (s := (U.val : Set X)) (t := (V.val : Set X)) i.le) := rfl

/-- The inclusions of open neighborhoods into `X` give a cocone of fundamental groups
with vertex the fundamental group of `X` at `x`. -/
def openNhdsCocone (x : X) : Cocone (openNhdsFunctor x) where
  pt := GrpCat.of (FundamentalGroup X x)
  ι :=
    { app := fun U => GrpCat.ofHom
        (map (ContinuousMap.subtypeVal (U.val : Set X)) (⟨x, U.property⟩ : U.val))
      naturality := by
        intro U V i
        apply GrpCat.hom_ext
        change (map (ContinuousMap.subtypeVal (V.val : Set X))
            (⟨x, V.property⟩ : V.val)).comp
            (map (ContinuousMap.inclusion
              (s := (U.val : Set X)) (t := (V.val : Set X)) i.le)
              (⟨x, U.property⟩ : U.val)) =
          map (ContinuousMap.subtypeVal (U.val : Set X)) (⟨x, U.property⟩ : U.val)
        exact (map_comp (ContinuousMap.subtypeVal (V.val : Set X))
          (ContinuousMap.inclusion
            (s := (U.val : Set X)) (t := (V.val : Set X)) i.le)
          (⟨x, U.property⟩ : U.val)).symm }

/-- The vertex of the neighborhood inclusion cocone is the ambient fundamental group. -/
@[simp]
theorem openNhdsCocone_pt (x : X) :
    (openNhdsCocone x).pt = GrpCat.of (FundamentalGroup X x) := rfl

/-- A leg of the neighborhood cocone is induced by the inclusion into the ambient space. -/
theorem openNhdsCocone_ι_app (x : X) (U : OpenNhds (X := TopCat.of X) x) :
    (openNhdsCocone x).ι.app U = GrpCat.ofHom
      (map (ContinuousMap.subtypeVal (U.val : Set X)) (⟨x, U.property⟩ : U.val)) := rfl

/-- The underlying homomorphism of a cocone leg is induced by the subtype map to `X`. -/
@[simp]
theorem openNhdsCocone_ι_app_hom (x : X) (U : OpenNhds (X := TopCat.of X) x) :
    ((openNhdsCocone x).ι.app U).hom =
      map (ContinuousMap.subtypeVal (U.val : Set X)) (⟨x, U.property⟩ : U.val) := rfl

/-- A cocone leg maps a loop class in a neighborhood to its class in the ambient space. -/
theorem openNhdsCocone_ι_app_hom_apply (x : X)
    (U : OpenNhds (X := TopCat.of X) x)
    (γ : FundamentalGroup U.val (⟨x, U.property⟩ : U.val)) :
    ((openNhdsCocone x).ι.app U).hom γ =
      Path.Homotopic.Quotient.map γ (ContinuousMap.subtypeVal (U.val : Set X)) := rfl

end FundamentalGroup
