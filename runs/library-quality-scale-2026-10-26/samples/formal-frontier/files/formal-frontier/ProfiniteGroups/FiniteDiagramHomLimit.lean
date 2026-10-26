/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.FiniteTargetHomColimit
public import Mathlib.CategoryTheory.Limits.Types.Yoneda

/-!
# Maps between limits of finite-space diagrams

A continuous map from a cofiltered limit of finite spaces to a limiting finite-space
diagram determines, at each target stage, a class of maps out of a source stage.
These classes are compatible along the arrows of the target diagram. The target
index need not be cofiltered, nonempty, or small.

The comparison concerns profinite spaces and continuous maps, not profinite groups.
Its inverse uses the limiting property of the specified target cone; it does not
choose a limit or a common source stage for every target coordinate.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1 (inverse-system and
  pro-category motivation, not this target-diagram equivalence as a stated result).
- Mathlib, `Mathlib.CategoryTheory.Limits.Types.Yoneda` and the filtered-colimit API used
  by `FiniteTargetHomColimit` (stage-map classes and compatible coordinates).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat

universe u w v t

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
variable {J : Type v} [Category.{t} J]

/-- Send a continuous map between specified limiting cones to its compatible
classes of finite-stage maps at the target objects. -/
noncomputable def stageHomLimitMap
    (F : I ⥤ FintypeCat.{max u w})
    (c : Cone (F ⋙ FintypeCat.toProfinite)) (hc : IsLimit c)
    (G : J ⥤ FintypeCat.{max u w})
    (d : Cone (G ⋙ FintypeCat.toProfinite))
    (f : c.pt ⟶ d.pt) : (G ⋙ stageHomFunctor F).sections :=
  ⟨fun j => (stageHomEquiv c hc (G.obj j)).symm (f ≫ d.π.app j), by
    intro j k arrow
    change stageHomPost (F := F) (G.map arrow)
        ((stageHomEquiv c hc (G.obj j)).symm (f ≫ d.π.app j)) =
      (stageHomEquiv c hc (G.obj k)).symm (f ≫ d.π.app k)
    apply (stageHomEquiv c hc (G.obj k)).injective
    simp only [stageHomEquiv_apply, stageHomToContinuous_naturality,
      stageHomEquiv_symm_apply]
    simpa only [Category.assoc, Functor.comp_map] using
      congrArg (fun h => f ≫ h) (d.w arrow)⟩

@[simp]
theorem stageHomLimitMap_apply
    (F : I ⥤ FintypeCat.{max u w})
    (c : Cone (F ⋙ FintypeCat.toProfinite)) (hc : IsLimit c)
    (G : J ⥤ FintypeCat.{max u w})
    (d : Cone (G ⋙ FintypeCat.toProfinite))
    (f : c.pt ⟶ d.pt) (j : J) :
    (stageHomLimitMap F c hc G d f).val j =
      (stageHomEquiv c hc (G.obj j)).symm (f ≫ d.π.app j) := rfl

/-- The target component of the comparison represents the composite with the
specified target projection. -/
@[simp]
theorem stageHomLimitMap_toContinuous
    (F : I ⥤ FintypeCat.{max u w})
    (c : Cone (F ⋙ FintypeCat.toProfinite)) (hc : IsLimit c)
    (G : J ⥤ FintypeCat.{max u w})
    (d : Cone (G ⋙ FintypeCat.toProfinite))
    (f : c.pt ⟶ d.pt) (j : J) :
    stageHomToContinuous c (G.obj j) ((stageHomLimitMap F c hc G d f).val j) =
      f ≫ d.π.app j := by
  simp

/-- The compatible classes of finite-stage maps determine a unique continuous
map to the specified limiting target cone. -/
theorem stageHomLimitMap_bijective
    (F : I ⥤ FintypeCat.{max u w})
    (c : Cone (F ⋙ FintypeCat.toProfinite)) (hc : IsLimit c)
    (G : J ⥤ FintypeCat.{max u w})
    (d : Cone (G ⋙ FintypeCat.toProfinite)) (hd : IsLimit d) :
    Function.Bijective (stageHomLimitMap F c hc G d) := by
  constructor
  · intro f g h
    apply hd.hom_ext
    intro j
    have hj := congrArg
      (fun x : (G ⋙ stageHomFunctor F).sections =>
        stageHomToContinuous c (G.obj j) (x.val j)) h
    simpa only [stageHomLimitMap_toContinuous] using hj
  · intro x
    let s : ((G ⋙ FintypeCat.toProfinite) ⋙
        coyoneda.obj (Opposite.op c.pt)).sections :=
      ⟨fun j => stageHomToContinuous c (G.obj j) (x.val j), by
        intro j k arrow
        change stageHomToContinuous c (G.obj j) (x.val j) ≫
          FintypeCat.toProfinite.map (G.map arrow) =
            stageHomToContinuous c (G.obj k) (x.val k)
        have hx := x.property arrow
        change stageHomPost (F := F) (G.map arrow) (x.val j) = x.val k at hx
        exact (stageHomToContinuous_naturality c (G.map arrow) (x.val j)).symm.trans
          (congrArg (stageHomToContinuous c (G.obj k)) hx)⟩
    refine ⟨hd.homEquiv.symm
      ((compCoyonedaSectionsEquiv (G ⋙ FintypeCat.toProfinite) c.pt) s), ?_⟩
    apply (Functor.sections_ext_iff).2
    intro j
    apply (stageHomEquiv c hc (G.obj j)).injective
    change stageHomToContinuous c (G.obj j)
        ((stageHomLimitMap F c hc G d
          (hd.homEquiv.symm
            ((compCoyonedaSectionsEquiv (G ⋙ FintypeCat.toProfinite) c.pt) s))).val j) =
      stageHomToContinuous c (G.obj j) (x.val j)
    exact (stageHomLimitMap_toContinuous F c hc G d _ j).trans
      (hd.homEquiv_symm_π_app
        ((compCoyonedaSectionsEquiv (G ⋙ FintypeCat.toProfinite) c.pt) s) j)

/-- Continuous maps into a limiting finite-space diagram correspond to
compatible target-stage classes of maps from finite source stages.

This extends `FiniteTargetHomColimit` with Mathlib’s limit/Yoneda API;
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1 motivates the inverse
systems but does not state this target-diagram comparison. -/
noncomputable def stageHomLimitEquiv
    (F : I ⥤ FintypeCat.{max u w})
    (c : Cone (F ⋙ FintypeCat.toProfinite)) (hc : IsLimit c)
    (G : J ⥤ FintypeCat.{max u w})
    (d : Cone (G ⋙ FintypeCat.toProfinite)) (hd : IsLimit d) :
    (c.pt ⟶ d.pt) ≃ (G ⋙ stageHomFunctor F).sections :=
  Equiv.ofBijective (stageHomLimitMap F c hc G d)
    (stageHomLimitMap_bijective F c hc G d hd)

@[simp]
theorem stageHomLimitEquiv_apply
    (F : I ⥤ FintypeCat.{max u w})
    (c : Cone (F ⋙ FintypeCat.toProfinite)) (hc : IsLimit c)
    (G : J ⥤ FintypeCat.{max u w})
    (d : Cone (G ⋙ FintypeCat.toProfinite)) (hd : IsLimit d)
    (f : c.pt ⟶ d.pt) :
    stageHomLimitEquiv F c hc G d hd f = stageHomLimitMap F c hc G d f := rfl

/-- The continuous map corresponding to a compatible family has, at a target
object, the continuous map represented by that family's component. -/
@[simp]
theorem stageHomLimitEquiv_symm_apply_projection
    (F : I ⥤ FintypeCat.{max u w})
    (c : Cone (F ⋙ FintypeCat.toProfinite)) (hc : IsLimit c)
    (G : J ⥤ FintypeCat.{max u w})
    (d : Cone (G ⋙ FintypeCat.toProfinite)) (hd : IsLimit d)
    (x : (G ⋙ stageHomFunctor F).sections) (j : J) :
    (stageHomLimitEquiv F c hc G d hd).symm x ≫ d.π.app j =
      stageHomToContinuous c (G.obj j) (x.val j) := by
  have h := (stageHomLimitEquiv F c hc G d hd).right_inv x
  have hj := congrArg (fun y : (G ⋙ stageHomFunctor F).sections => y.val j) h
  have hcont := congrArg (stageHomToContinuous c (G.obj j)) hj
  change stageHomToContinuous c (G.obj j)
    ((stageHomLimitMap F c hc G d
      ((stageHomLimitEquiv F c hc G d hd).symm x)).val j) =
      stageHomToContinuous c (G.obj j) (x.val j) at hcont
  rwa [stageHomLimitMap_toContinuous] at hcont

/-- A representative of one target component yields the corresponding
composite of source and target projections. -/
theorem stageHomLimitEquiv_symm_apply_class
    (F : I ⥤ FintypeCat.{max u w})
    (c : Cone (F ⋙ FintypeCat.toProfinite)) (hc : IsLimit c)
    (G : J ⥤ FintypeCat.{max u w})
    (d : Cone (G ⋙ FintypeCat.toProfinite)) (hd : IsLimit d)
    (x : (G ⋙ stageHomFunctor F).sections) (j : J)
    (i : I) (g : F.obj i ⟶ G.obj j)
    (hx : x.val j = stageHomClass F (G.obj j) i g) :
    (stageHomLimitEquiv F c hc G d hd).symm x ≫ d.π.app j =
      c.π.app i ≫ FintypeCat.toProfinite.map g := by
  rw [stageHomLimitEquiv_symm_apply_projection, hx, stageHomToContinuous_class]

end Profinite
