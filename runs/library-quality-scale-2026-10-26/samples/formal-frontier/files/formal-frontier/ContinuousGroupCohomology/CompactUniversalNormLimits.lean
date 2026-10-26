/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.RestrictedLevelCompactFunctoriality
public import ContinuousGroupCohomology.CompactAddCommGroupLimits
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Universal norms and compact relative-norm limits

The range of a projection of the full invariant relative-norm limit is the
universal-norm submodule. Consequently relative norms between universal-norm
coefficients are surjective, and every closed norm-compatible restricted system
containing universal norms has canonically the same compact additive-group limit
as the full invariant system. All level topologies are the chosen invariant
topologies of the level-compact representation.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.RestrictedLevelCompactRep

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

local instance : Nonempty (OpenNormalSubgroup G) :=
  ⟨⟨⊤, by change (⊤ : Subgroup G).Normal; infer_instance⟩⟩

noncomputable local instance :
    HasLimitsOfShape (OpenNormalSubgroup G) CompHausAddCommGrp.{u} :=
  ⟨fun _ => inferInstance⟩

private theorem fullNorm_map_coe (A : LevelCompactRep.{u, u, u} R G)
    (U V : OpenNormalSubgroup G) (hVU : V ≤ U)
    (y : (full A).system.coefficients V) :
    (((restrictedNormDiagram (full A)).map (homOfLE hVU) y :
      (full A).system.coefficients U).1 :
      openSubgroupInvariants A.rep U.toOpenSubgroup) =
        LevelCompact.relativeNorm A.rep U.toOpenSubgroup V.toOpenSubgroup hVU y.1 := by
  have hmap := ConcreteCategory.congr_hom
    (restrictedNormDiagram_map (full A) (homOfLE hVU)) y
  have hp := congrArg (fun t : (restrictedNormDiagram (full A)).obj U =>
      ((t : (full A).system.coefficients U).1 :
        openSubgroupInvariants A.rep U.toOpenSubgroup)) hmap
  calc
    _ = (((full A).system.relativeNormHom U V hVU y :
        (full A).system.coefficients U).1 :
          openSubgroupInvariants A.rep U.toOpenSubgroup) := hp
    _ = (((full A).system.relativeNorm U V hVU y).1 :
          openSubgroupInvariants A.rep U.toOpenSubgroup) := by
      exact congrArg (fun t : (full A).system.coefficients U =>
        (t.1 : openSubgroupInvariants A.rep U.toOpenSubgroup))
          ((full A).system.relativeNormHom_apply U V hVU y)
    _ = _ := (full A).system.relativeNorm_coe U V hVU y

private theorem fullNorm_range_iff (A : LevelCompactRep.{u, u, u} R G)
    (U V : OpenNormalSubgroup G) (hVU : V ≤ U)
    (x : (full A).system.coefficients U) :
    x ∈ Set.range ((restrictedNormDiagram (full A)).map (homOfLE hVU)) ↔
      (x.1 : openSubgroupInvariants A.rep U.toOpenSubgroup) ∈
        LinearMap.range (LevelCompact.relativeNorm A.rep U.toOpenSubgroup
          V.toOpenSubgroup hVU) := by
  constructor
  · rintro ⟨y, hy⟩
    let yCoeff : (full A).system.coefficients V := y
    refine ⟨(yCoeff.1 : openSubgroupInvariants A.rep V.toOpenSubgroup), ?_⟩
    have hp := congrArg (fun t : (restrictedNormDiagram (full A)).obj U =>
        ((t : (full A).system.coefficients U).1 :
          openSubgroupInvariants A.rep U.toOpenSubgroup)) hy
    exact (fullNorm_map_coe A U V hVU yCoeff).symm.trans hp
  · rintro ⟨y, hy⟩
    let z : (full A).system.coefficients V := by
      change (LevelCompact.fullRestrictedLevelSystem A.rep A.levelCompact).coefficients V
      exact ⟨y, Submodule.mem_top⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact (fullNorm_map_coe A U V hVU z).trans hy

/-- A full compact relative-norm limit projects precisely onto the universal
norms, viewed inside the full invariant coefficient at an open normal level. -/
theorem fullNormLimit_projection_mem_iff (A : LevelCompactRep.{u, u, u} R G)
    (U : OpenNormalSubgroup G) (x : (full A).system.coefficients U) :
    x ∈ Set.range (limit.π (restrictedNormDiagram (full A)) U) ↔
      (x.1 : openSubgroupInvariants A.rep U.toOpenSubgroup) ∈
        LevelCompact.universalNormSubmodule A.rep U := by
  let xObj : (restrictedNormDiagram (full A)).obj U := x
  let xUnderlying : openSubgroupInvariants A.rep U.toOpenSubgroup := x.1
  change xObj ∈ Set.range (limit.π (restrictedNormDiagram (full A)) U) ↔
    xUnderlying ∈ LevelCompact.universalNormSubmodule A.rep U
  rw [CompHausAddCommGrp.limit_π_range_eq_eventualRange.{u,u}
    (restrictedNormDiagram (full A)) U,
    LevelCompact.mem_universalNormSubmodule_iff]
  rw [CategoryTheory.Functor.mem_eventualRange_iff]
  constructor
  · intro hx V hVU
    exact (fullNorm_range_iff A U V hVU x).mp (hx (homOfLE hVU))
  · intro hx V hVU
    exact (fullNorm_range_iff A U V (leOfHom hVU) x).mpr (hx V (leOfHom hVU))

/-- Every restricted universal norm is the relative norm of another universal
norm at any prescribed deeper open normal level. -/
theorem universalNorm_relativeNorm_surjective (A : LevelCompactRep.{u, u, u} R G)
    (U V : OpenNormalSubgroup G) (hVU : V ≤ U) :
    Function.Surjective ((universalNorm A).system.relativeNorm U V hVU) := by
  intro x
  let y : (full A).system.coefficients U := by
    change (LevelCompact.fullRestrictedLevelSystem A.rep A.levelCompact).coefficients U
    exact ⟨x.1, Submodule.mem_top⟩
  obtain ⟨s, hs⟩ := (fullNormLimit_projection_mem_iff A U y).mpr (by
    exact x.2)
  let z : (universalNorm A).system.coefficients V := by
    let fullCoeff : (full A).system.coefficients V :=
      limit.π (restrictedNormDiagram (full A)) V s
    refine ⟨fullCoeff.1, ?_⟩
    change _ ∈ LevelCompact.universalNormSubmodule A.rep V
    exact (fullNormLimit_projection_mem_iff A V _).mp ⟨s, rfl⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  have hpoint : (restrictedNormDiagram (full A)).map (homOfLE hVU)
      (limit.π (restrictedNormDiagram (full A)) V s) =
        limit.π (restrictedNormDiagram (full A)) U s := by
    exact ConcreteCategory.congr_hom
      (limit.w (restrictedNormDiagram (full A)) (homOfLE hVU)) s
  have hpoint' := congrArg
    (fun t : (restrictedNormDiagram (full A)).obj U =>
      ((t : (full A).system.coefficients U).1 :
        openSubgroupInvariants A.rep U.toOpenSubgroup)) hpoint
  have hs' := congrArg
    (fun t : (restrictedNormDiagram (full A)).obj U =>
      ((t : (full A).system.coefficients U).1 :
        openSubgroupInvariants A.rep U.toOpenSubgroup)) hs
  have hsource : (z.1 : openSubgroupInvariants A.rep V.toOpenSubgroup) =
      ((limit.π (restrictedNormDiagram (full A)) V s :
        (full A).system.coefficients V).1 :
          openSubgroupInvariants A.rep V.toOpenSubgroup) := rfl
  have huni : (((universalNorm A).system.relativeNorm U V hVU z).1 :
      openSubgroupInvariants A.rep U.toOpenSubgroup) =
        LevelCompact.relativeNorm A.rep U.toOpenSubgroup V.toOpenSubgroup hVU
          (z.1 : openSubgroupInvariants A.rep V.toOpenSubgroup) :=
    (universalNorm A).system.relativeNorm_coe U V hVU z
  have hstep : LevelCompact.relativeNorm A.rep U.toOpenSubgroup
      V.toOpenSubgroup hVU (z.1 : openSubgroupInvariants A.rep V.toOpenSubgroup) =
    LevelCompact.relativeNorm A.rep U.toOpenSubgroup V.toOpenSubgroup hVU
      ((limit.π (restrictedNormDiagram (full A)) V s :
        (full A).system.coefficients V).1 :
          openSubgroupInvariants A.rep V.toOpenSubgroup) :=
    congrArg _ hsource
  exact huni.trans (hstep.trans ((fullNorm_map_coe A U V hVU
    (limit.π (restrictedNormDiagram (full A)) V s)).symm.trans
      ((hpoint'.trans hs').trans (rfl : y.1 = x.1))))

/-- Identity on the underlying representation, from a selected system into
the full invariant system. -/
@[expose] def fullInclusion (B : RestrictedLevelCompactRep R G) :
    B ⟶ full B.toLevelCompactRep where
  hom := 𝟙 B.toLevelCompactRep
  map_mem := by
    intro U x hx
    change _ ∈ (⊤ : Submodule R (openSubgroupInvariants B.rep U.toOpenSubgroup))
    exact Submodule.mem_top

@[simp] theorem fullInclusion_apply (B : RestrictedLevelCompactRep R G)
    (U : OpenNormalSubgroup G) (x : B.system.coefficients U) :
    ((groupMap (fullInclusion B) U x :
        (full B.toLevelCompactRep).system.coefficients U).1 :
          openSubgroupInvariants B.rep U.toOpenSubgroup) = x.1 := by
  rw [groupMap_apply, coefficientMap_coe]
  change ((Rep.invariantsFunctor R U.toOpenSubgroup).map
      ((Rep.resFunctor U.toOpenSubgroup.subtype).map (𝟙 B.rep))).hom x.1 = x.1
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

/-- Projection of the canonical comparison on any chosen level; the component
is the actual continuous coefficient inclusion. -/
@[reassoc] theorem fullInclusion_limitMap_π (B : RestrictedLevelCompactRep R G)
    (U : OpenNormalSubgroup G) :
    lim.map (restrictedNormDiagramMap (fullInclusion B)) ≫
        limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U =
      limit.π (restrictedNormDiagram B) U ≫ groupMap (fullInclusion B) U := by
  exact limit.map_π (restrictedNormDiagramMap (fullInclusion B)) U

private theorem normLimit_element_ext (B : RestrictedLevelCompactRep R G)
    (x y : (limit (restrictedNormDiagram B) : CompHausAddCommGrp))
    (h : ∀ U, limit.π (restrictedNormDiagram B) U x =
      limit.π (restrictedNormDiagram B) U y) : x = y := by
  let t : LimitCone (restrictedNormDiagram B) :=
    ⟨CompHausAddCommGrp.limitCone _, CompHausAddCommGrp.limitConeIsLimit _⟩
  let e := limit.isoLimitCone t
  apply ((CategoryTheory.forget CompHausAddCommGrp).mapIso e).toEquiv.injective
  apply Subtype.ext
  funext U
  have hx := ConcreteCategory.congr_hom (limit.isoLimitCone_hom_π t U) x
  have hy := ConcreteCategory.congr_hom (limit.isoLimitCone_hom_π t U) y
  exact hx.trans ((h U).trans hy.symm)

private theorem normDiagram_map_coe (B : RestrictedLevelCompactRep R G)
    (U V : OpenNormalSubgroup G) (hVU : V ≤ U)
    (x : B.system.coefficients V) :
    (((restrictedNormDiagram B).map (homOfLE hVU) x :
      B.system.coefficients U).1 :
        openSubgroupInvariants B.rep U.toOpenSubgroup) =
      LevelCompact.relativeNorm B.rep U.toOpenSubgroup V.toOpenSubgroup hVU x.1 := by
  have hmap := ConcreteCategory.congr_hom
    (restrictedNormDiagram_map B (homOfLE hVU)) x
  have hp := congrArg (fun t : (restrictedNormDiagram B).obj U =>
      ((t : B.system.coefficients U).1 :
        openSubgroupInvariants B.rep U.toOpenSubgroup)) hmap
  calc
    _ = (((B.system.relativeNormHom U V hVU x : B.system.coefficients U).1) :
      openSubgroupInvariants B.rep U.toOpenSubgroup) := hp
    _ = ((B.system.relativeNorm U V hVU x).1 :
      openSubgroupInvariants B.rep U.toOpenSubgroup) := by
      exact congrArg (fun t : B.system.coefficients U =>
        (t.1 : openSubgroupInvariants B.rep U.toOpenSubgroup))
          (B.system.relativeNormHom_apply U V hVU x)
    _ = _ := B.system.relativeNorm_coe U V hVU x

private def fullPoint_coefficient (B : RestrictedLevelCompactRep R G)
    (s : (limit (restrictedNormDiagram (full B.toLevelCompactRep)) :
      CompHausAddCommGrp)) (U : OpenNormalSubgroup G) : B.system.coefficients U := by
  let x : (full B.toLevelCompactRep).system.coefficients U :=
    limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U s
  exact ⟨x.1, B.system.universalNorm_le U
    ((fullNormLimit_projection_mem_iff B.toLevelCompactRep U x).mp ⟨s, rfl⟩)⟩

private theorem fullPoint_coefficient_compatible (B : RestrictedLevelCompactRep R G)
    (s : (limit (restrictedNormDiagram (full B.toLevelCompactRep)) :
      CompHausAddCommGrp)) {V U : OpenNormalSubgroup G} (hVU : V ⟶ U) :
    (restrictedNormDiagram B).map hVU (fullPoint_coefficient B s V) =
      fullPoint_coefficient B s U := by
  apply Subtype.ext
  have hfull := congrArg
    (fun t : (restrictedNormDiagram (full B.toLevelCompactRep)).obj U =>
      ((t : (full B.toLevelCompactRep).system.coefficients U).1 :
        openSubgroupInvariants B.rep U.toOpenSubgroup))
    (ConcreteCategory.congr_hom
      (limit.w (restrictedNormDiagram (full B.toLevelCompactRep)) hVU) s)
  have hsource : ((fullPoint_coefficient B s V).1 :
      openSubgroupInvariants B.rep V.toOpenSubgroup) =
      ((limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) V s :
        (full B.toLevelCompactRep).system.coefficients V).1 :
          openSubgroupInvariants B.rep V.toOpenSubgroup) := rfl
  have hnormB := normDiagram_map_coe B U V (leOfHom hVU)
    (fullPoint_coefficient B s V)
  have hsourceNorm := congrArg
    (LevelCompact.relativeNorm B.rep U.toOpenSubgroup V.toOpenSubgroup (leOfHom hVU))
      hsource
  have hnormF := fullNorm_map_coe B.toLevelCompactRep U V (leOfHom hVU)
    (limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) V s)
  have htarget : ((limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U s :
      (full B.toLevelCompactRep).system.coefficients U).1 :
        openSubgroupInvariants B.rep U.toOpenSubgroup) =
          (fullPoint_coefficient B s U).1 := rfl
  exact hnormB.trans (hsourceNorm.trans (hnormF.symm.trans (hfull.trans htarget)))

private def fullPoint_inRestrictedCone (B : RestrictedLevelCompactRep R G)
    (s : (limit (restrictedNormDiagram (full B.toLevelCompactRep)) :
      CompHausAddCommGrp)) :
    (CompHausAddCommGrp.limitCone.{u,u} (restrictedNormDiagram B)).pt := by
  refine ⟨fun U => fullPoint_coefficient B s U, ?_⟩
  intro V U hVU
  exact fullPoint_coefficient_compatible B s hVU

/-- The map of compact limits induced by levelwise inclusion is bijective:
compatible full families lie in every universal-norm range simultaneously. -/
theorem fullInclusion_limitMap_bijective
    (B : RestrictedLevelCompactRep R G) :
    Function.Bijective
      (lim.map (restrictedNormDiagramMap (fullInclusion B))) := by
  constructor
  · intro x y heq
    apply normLimit_element_ext B x y
    intro U
    have hπ := congrArg (fun t =>
      limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U t) heq
    have hx := ConcreteCategory.congr_hom (fullInclusion_limitMap_π B U) x
    have hy := ConcreteCategory.congr_hom (fullInclusion_limitMap_π B U) y
    have hmaps : groupMap (fullInclusion B) U
          (limit.π (restrictedNormDiagram B) U x) =
        groupMap (fullInclusion B) U
          (limit.π (restrictedNormDiagram B) U y) :=
      hx.symm.trans (hπ.trans hy)
    apply Subtype.ext
    have hval := congrArg
      (fun t : (restrictedNormDiagram (full B.toLevelCompactRep)).obj U =>
        ((t : (full B.toLevelCompactRep).system.coefficients U).1 :
          openSubgroupInvariants B.rep U.toOpenSubgroup)) hmaps
    have hval' : ((groupMap (fullInclusion B) U
          (limit.π (restrictedNormDiagram B) U x) :
        (full B.toLevelCompactRep).system.coefficients U).1 :
          openSubgroupInvariants B.rep U.toOpenSubgroup) =
      ((groupMap (fullInclusion B) U
          (limit.π (restrictedNormDiagram B) U y) :
        (full B.toLevelCompactRep).system.coefficients U).1 :
          openSubgroupInvariants B.rep U.toOpenSubgroup) := by
      simpa only [full] using hval
    exact (fullInclusion_apply B U _).symm.trans
      (hval'.trans (fullInclusion_apply B U _))
  · intro s
    let cone : LimitCone (restrictedNormDiagram B) :=
      ⟨CompHausAddCommGrp.limitCone.{u,u} _, CompHausAddCommGrp.limitConeIsLimit _⟩
    let pre : (limit (restrictedNormDiagram B) : CompHausAddCommGrp) :=
      (limit.isoLimitCone cone).inv (fullPoint_inRestrictedCone B s)
    refine ⟨pre, ?_⟩
    apply normLimit_element_ext (full B.toLevelCompactRep)
    intro U
    have hpre : limit.π (restrictedNormDiagram B) U pre =
        fullPoint_coefficient B s U := by
      exact ConcreteCategory.congr_hom (limit.isoLimitCone_inv_π cone U)
        (fullPoint_inRestrictedCone B s)
    have hπ := ConcreteCategory.congr_hom (fullInclusion_limitMap_π B U) pre
    change limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U
        (lim.map (restrictedNormDiagramMap (fullInclusion B)) pre) =
          groupMap (fullInclusion B) U (limit.π (restrictedNormDiagram B) U pre)
      at hπ
    have hmaps : limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U
        (lim.map (restrictedNormDiagramMap (fullInclusion B)) pre) =
          groupMap (fullInclusion B) U (fullPoint_coefficient B s U) :=
      hπ.trans (congrArg (groupMap (fullInclusion B) U) hpre)
    apply Subtype.ext
    have hval := congrArg
      (fun t : (restrictedNormDiagram (full B.toLevelCompactRep)).obj U =>
        ((t : (full B.toLevelCompactRep).system.coefficients U).1 :
          openSubgroupInvariants B.rep U.toOpenSubgroup)) hmaps
    exact hval.trans ((fullInclusion_apply B U _).trans rfl)

/-- A continuous additive bijection of compact Hausdorff additive groups is an
isomorphism; its inverse is continuous and additive. -/
theorem compactGroup_isIso_of_bijective {X Y : CompHausAddCommGrp.{u}}
    (f : X ⟶ Y) (h : Function.Bijective f) : IsIso f := by
  let e := CompHausLike.isoOfBijective
    ((forget₂ CompHausAddCommGrp CompHaus).map f) h
  let inverseFunction : Y → X := fun y => e.inv y
  have hr (y : Y) : f (inverseFunction y) = y := Iso.inv_hom_id_apply e y
  have hl (x : X) : inverseFunction (f x) = x := Iso.hom_inv_id_apply e x
  let inverse : Y ⟶ X := ConcreteCategory.ofHom
    { toAddMonoidHom :=
        { toFun := inverseFunction
          map_zero' := by
            apply h.1
            simpa only [map_zero] using hr (0 : Y)
          map_add' := by
            intro a b
            apply h.1
            calc
              f (inverseFunction (a + b)) = a + b := hr (a + b)
              _ = f (inverseFunction a) + f (inverseFunction b) := by rw [hr a, hr b]
              _ = f (inverseFunction a + inverseFunction b) := (f.hom.map_add _ _).symm }
      continuous_toFun := e.inv.hom.hom.continuous }
  exact ⟨⟨inverse, by
    apply CompHausAddCommGrp.hom_ext
    ext x
    exact hl x, by
    apply CompHausAddCommGrp.hom_ext
    ext y
    exact hr y⟩⟩

/-- The canonical inclusion of every closed norm-compatible restricted system
into the full invariant system induces an isomorphism of the actual compact
Hausdorff additive inverse limits. -/
@[expose] def restrictedNormLimitIso (B : RestrictedLevelCompactRep R G) :
    limit (restrictedNormDiagram B) ≅
      limit (restrictedNormDiagram (full B.toLevelCompactRep)) := by
  let comparison := lim.map (restrictedNormDiagramMap (fullInclusion B))
  letI : IsIso comparison :=
    compactGroup_isIso_of_bijective comparison (fullInclusion_limitMap_bijective B)
  exact asIso comparison

/-- The forward comparison projection is the actual levelwise inclusion. -/
@[reassoc] theorem restrictedNormLimitIso_hom_π
    (B : RestrictedLevelCompactRep R G) (U : OpenNormalSubgroup G) :
    (restrictedNormLimitIso B).hom ≫
        limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U =
      limit.π (restrictedNormDiagram B) U ≫ groupMap (fullInclusion B) U :=
  fullInclusion_limitMap_π B U

/-- Each inverse-limit coordinate is uniquely determined by its image under
the genuine levelwise coefficient inclusion. -/
@[reassoc] theorem restrictedNormLimitIso_inv_π
    (B : RestrictedLevelCompactRep R G) (U : OpenNormalSubgroup G) :
    (restrictedNormLimitIso B).inv ≫ limit.π (restrictedNormDiagram B) U ≫
        groupMap (fullInclusion B) U =
      limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U := by
  have hcomm := congrArg
    (fun m : limit (restrictedNormDiagram B) ⟶
        (restrictedNormDiagram (full B.toLevelCompactRep)).obj U =>
      (restrictedNormLimitIso B).inv ≫ m)
        (restrictedNormLimitIso_hom_π B U)
  have hcancel : (restrictedNormLimitIso B).inv ≫
      ((restrictedNormLimitIso B).hom ≫
        limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U) =
          limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U := by
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact hcomm.symm.trans hcancel

/-- Inclusion into the full system commutes with any morphism of chosen
restricted systems. Its chosen-coefficient preservation is provided by `f`. -/
@[reassoc] theorem fullInclusion_naturality {B C : RestrictedLevelCompactRep R G}
    (f : B ⟶ C) :
    f ≫ fullInclusion C =
      fullInclusion B ≫ fullFunctor.map (forget.map f) := by
  apply Hom.ext
  change f.hom ≫ (𝟙 C.toLevelCompactRep) =
    (𝟙 B.toLevelCompactRep) ≫ f.hom
  simp

/-- Coefficient naturality of the canonical compact-limit comparison.
On universal-norm systems every level-compact coefficient morphism supplies
the required restricted morphism automatically. -/
@[reassoc] theorem restrictedNormLimitIso_naturality
    {B C : RestrictedLevelCompactRep R G} (f : B ⟶ C) :
    lim.map (restrictedNormDiagramMap f) ≫ (restrictedNormLimitIso C).hom =
      (restrictedNormLimitIso B).hom ≫
        lim.map (restrictedNormDiagramMap
          (fullFunctor.map (forget.map f))) := by
  let D : RestrictedLevelCompactRep R G ⥤ CompHausAddCommGrp.{u} :=
    restrictedNormDiagramFunctor ⋙ lim
  change D.map f ≫ D.map (fullInclusion C) =
    D.map (fullInclusion B) ≫ D.map (fullFunctor.map (forget.map f))
  have h := congrArg D.map (fullInclusion_naturality f)
  rw [D.map_comp f (fullInclusion C)] at h
  exact h.trans (D.map_comp (fullInclusion B) (fullFunctor.map (forget.map f)))

/-- Universal norms admit the canonical comparison naturally for *all*
level-compact coefficient morphisms, via the published preservation functor. -/
@[reassoc] theorem universalNorm_limitIso_naturality
    {A C : LevelCompactRep.{u, u, u} R G} (f : A ⟶ C) :
    lim.map (restrictedNormDiagramMap (universalNormFunctor.map f)) ≫
        (restrictedNormLimitIso (universalNormFunctor.obj C)).hom =
      (restrictedNormLimitIso (universalNormFunctor.obj A)).hom ≫
        lim.map (restrictedNormDiagramMap
          (fullFunctor.map (forget.map (universalNormFunctor.map f)))) :=
  restrictedNormLimitIso_naturality (universalNormFunctor.map f)

end ContinuousGroupCohomology.RestrictedLevelCompactRep
