/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Builds on the generic cylinder, native restriction, and coefficient comparisons.
-/


module
public import SheafCohomology.NativeCommRingCylinderSections
public import SheafCohomology.NativeAdditiveCylinderSections

public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Open naturality for native cylinder sections

At a fixed stage and for an arbitrary original cone, the actual restricted-stage
section diagrams vary contravariantly with the open. Their colimits compare
naturally with the original cone's sections on inverse-image opens.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
variable {C : Type (v + 1)} [Category.{v} C]
variable (S : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C) (i0 : ι)

/-- The sections of the literal restricted tail stages over a named base open. -/
abbrev cylinderSections (W : Opens (S.obj (op i0))) : Set.Ici i0 ⥤ C :=
  (restricted S i0 W).rightOp ⋙ SheafedSpace.Γ

private theorem namedSectionRestriction_naturality
    {X Y : SheafedSpace.{v + 1, v, v} C} (g : X ⟶ Y)
    {U V : Opens Y} (h : U ≤ V) {U' V' : Opens X}
    (hU : U' = (Opens.map g.hom.base).obj U)
    (hV : V' = (Opens.map g.hom.base).obj V) (h' : U' ≤ V') :
    g.hom.c.app (op V) ≫
      eqToHom (congrArg (fun O : Opens X => X.presheaf.obj (op O)) hV.symm) ≫
        X.presheaf.map (homOfLE h').op =
    Y.presheaf.map (homOfLE h).op ≫ g.hom.c.app (op U) ≫
      eqToHom (congrArg (fun O : Opens X => X.presheaf.obj (op O)) hU.symm) := by
  cases hU
  cases hV
  have hn := g.hom.c.naturality (homOfLE h).op
  change Y.presheaf.map (homOfLE h).op ≫ g.hom.c.app (op U) =
    g.hom.c.app (op V) ≫
      X.presheaf.map ((Opens.map g.hom.base).map (homOfLE h)).op at hn
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
    Opens.map_homOfLE] using hn.symm

private theorem presheaf_cast_restrict (X : SheafedSpace.{v + 1, v, v} C)
    {A B D E : Opens X} (eA : A = D) (eB : B = E)
    (h : A ≤ B) (h' : D ≤ E) :
    X.presheaf.map (homOfLE h).op ≫
      eqToHom (congrArg (fun O : Opens X => X.presheaf.obj (op O)) eA) =
    eqToHom (congrArg (fun O : Opens X => X.presheaf.obj (op O)) eB) ≫
      X.presheaf.map (homOfLE h').op := by
  cases eA
  cases eB
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

omit [IsDirectedOrder ι] in
/-- Pullback of a named base open preserves inclusion at every tail stage. -/
theorem stageOpen_mono {U V : Opens (S.obj (op i0))} (h : U ≤ V)
    (i : Set.Ici i0) : stageOpen S i0 U i ≤ stageOpen S i0 V i := by
  let base : Set.Ici i0 := ⟨i0, le_refl i0⟩
  let arrow : (op i : (Set.Ici i0)ᵒᵖ) ⟶ op base := (homOfLE i.property).op
  have hU := stageOpen_map S i0 U arrow
  have hV := stageOpen_map S i0 V arrow
  rw [stageOpen_base S i0 U] at hU
  rw [stageOpen_base S i0 V] at hV
  rw [hU, hV]
  exact leOfHom ((Opens.map ((tailDiagram S i0).map arrow).hom.base).map (homOfLE h))

/-- A component of the original-stage restriction, with both object transports. -/
@[expose] def stageSectionRestriction (U V : Opens (S.obj (op i0))) (h : U ≤ V)
    (i : Set.Ici i0) : (cylinderSections S i0 V).obj i ⟶
      (cylinderSections S i0 U).obj i :=
  eqToHom (SheafedSpace.restrict_Γ_obj (S.obj (op i.1)) (stageOpen S i0 V i)) ≫
    (S.obj (op i.1)).presheaf.map
      (homOfLE (stageOpen_mono S i0 h i)).op ≫
    eqToHom (SheafedSpace.restrict_Γ_obj (S.obj (op i.1)) (stageOpen S i0 U i)).symm

omit [IsDirectedOrder ι] in
private theorem stageMap_eq_named (W : Opens (S.obj (op i0)))
    {i j : (Set.Ici i0)ᵒᵖ} (f : i ⟶ j) :
    stageMap S i0 W f = SheafedSpace.restrictOnNamedPreimage
      ((tailDiagram S i0).map f) (stageOpen S i0 W (unop j))
      (stageOpen S i0 W (unop i)) (stageOpen_map S i0 W f) := by
  haveI : Mono ((S.obj (op (unop j).1)).ofRestrict
      (stageOpen S i0 W (unop j)).isOpenEmbedding) := inferInstance
  apply (cancel_mono ((S.obj (op (unop j).1)).ofRestrict
    (stageOpen S i0 W (unop j)).isOpenEmbedding)).1
  exact (stageMap_fac S i0 W f).trans
    (SheafedSpace.restrictOnNamedPreimage_fac
      ((tailDiagram S i0).map f) (stageOpen S i0 W (unop j))
      (stageOpen S i0 W (unop i)) (stageOpen_map S i0 W f)).symm

omit [IsDirectedOrder ι] in
private theorem stageMap_sections (W : Opens (S.obj (op i0)))
    {i j : Set.Ici i0} (f : i ⟶ j) :
    eqToHom (SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 W i)).symm ≫
      (cylinderSections S i0 W).map f ≫
      eqToHom (SheafedSpace.restrict_Γ_obj
        (S.obj (op j.1)) (stageOpen S i0 W j)) =
    ((tailDiagram S i0).map f.op).hom.c.app (op (stageOpen S i0 W i)) ≫
      eqToHom (congrArg
        (fun O : Opens (S.obj (op j.1)) => (S.obj (op j.1)).presheaf.obj (op O))
        (stageOpen_map S i0 W f.op).symm) := by
  change eqToHom (SheafedSpace.restrict_Γ_obj
      (S.obj (op i.1)) (stageOpen S i0 W i)).symm ≫
    SheafedSpace.Γ.map (stageMap S i0 W f.op).op ≫
    eqToHom (SheafedSpace.restrict_Γ_obj
      (S.obj (op j.1)) (stageOpen S i0 W j)) = _
  rw [stageMap_eq_named S i0 W f.op]
  exact SheafedSpace.restrictOnNamedPreimage_Γ_map
    ((tailDiagram S i0).map f.op) (stageOpen S i0 W i)
    (stageOpen S i0 W j) (stageOpen_map S i0 W f.op)

/-- Original-stage restrictions commute with every named-preimage transition. -/
@[expose] def stageSectionsRestriction (U V : Opens (S.obj (op i0))) (h : U ≤ V) :
    cylinderSections S i0 V ⟶ cylinderSections S i0 U where
  app i := stageSectionRestriction S i0 U V h i
  naturality := by
    intro i j f
    haveI : Epi (eqToHom (SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 V i)).symm) := inferInstance
    haveI : Mono (eqToHom (SheafedSpace.restrict_Γ_obj
        (S.obj (op j.1)) (stageOpen S i0 U j))) := inferInstance
    apply (cancel_epi (eqToHom (SheafedSpace.restrict_Γ_obj
      (S.obj (op i.1)) (stageOpen S i0 V i)).symm)).1
    apply (cancel_mono (eqToHom (SheafedSpace.restrict_Γ_obj
      (S.obj (op j.1)) (stageOpen S i0 U j)))).1
    simp only [stageSectionRestriction, Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id]
    have hV := stageMap_sections S i0 V f
    have hU := stageMap_sections S i0 U f
    have hn := namedSectionRestriction_naturality
      ((tailDiagram S i0).map f.op) (stageOpen_mono S i0 h i)
      (stageOpen_map S i0 U f.op) (stageOpen_map S i0 V f.op)
      (stageOpen_mono S i0 h j)
    simp only [← Category.assoc, hV, hU]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp]
    convert hn using 1
    all_goals rfl

omit [IsDirectedOrder ι] in
/-- Restricting from an open to itself is the identity stage transformation. -/
theorem stageSectionsRestriction_id (U : Opens (S.obj (op i0))) :
    stageSectionsRestriction S i0 U U (le_refl U) = 𝟙 (cylinderSections S i0 U) := by
  ext i
  simp [stageSectionsRestriction, stageSectionRestriction]

omit [IsDirectedOrder ι] in
/-- Successive open restrictions compose in the same order as presheaf maps. -/
theorem stageSectionsRestriction_comp (U V W : Opens (S.obj (op i0)))
    (hUV : U ≤ V) (hVW : V ≤ W) :
    stageSectionsRestriction S i0 V W hVW ≫
      stageSectionsRestriction S i0 U V hUV =
        stageSectionsRestriction S i0 U W (hUV.trans hVW) := by
  ext i
  have hmap :
      (S.obj (op i.1)).presheaf.map (homOfLE (stageOpen_mono S i0 hVW i)).op ≫
          (S.obj (op i.1)).presheaf.map (homOfLE (stageOpen_mono S i0 hUV i)).op =
        (S.obj (op i.1)).presheaf.map
          (homOfLE (stageOpen_mono S i0 (hUV.trans hVW) i)).op := by
    rw [← Functor.map_comp]
    congr 1
  have hwrapped := congrArg
    (fun arrow => eqToHom (SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 W i)) ≫ arrow ≫
      eqToHom (SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 U i)).symm) hmap
  simpa [stageSectionsRestriction, stageSectionRestriction, Category.assoc]
    using hwrapped

variable (m : Cone S)

/-- The original cone's restricted projection gives a generic cocone of sections. -/
@[expose] def cylinderSectionsCocone (W : Opens (S.obj (op i0))) :
    Cocone (cylinderSections S i0 W) where
  pt := m.pt.presheaf.obj (op (coneOpen S i0 m W))
  ι := {
    app i := SheafedSpace.Γ.map ((restrictedCone S i0 m W).π.app (op i)).op ≫
      eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m W))
    naturality := by
      intro i j f
      change SheafedSpace.Γ.map ((restricted S i0 W).map f.op).op ≫
          (SheafedSpace.Γ.map ((restrictedCone S i0 m W).π.app (op j)).op ≫
            eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m W))) =
        (SheafedSpace.Γ.map ((restrictedCone S i0 m W).π.app (op i)).op ≫
          eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m W))) ≫ 𝟙 _
      rw [Category.comp_id, ← Category.assoc, ← SheafedSpace.Γ.map_comp]
      congr 1
      rw [← op_comp, (restrictedCone S i0 m W).w f.op]
  }

/-- The comparison induced by the original cone, without a limiting assumption. -/
@[expose] def cylinderSectionsComparison (W : Opens (S.obj (op i0)))
    [HasColimit (cylinderSections S i0 W)] :
    colimit (cylinderSections S i0 W) ⟶
      m.pt.presheaf.obj (op (coneOpen S i0 m W)) :=
  colimit.desc _ (cylinderSectionsCocone S i0 m W)

omit [IsDirectedOrder ι] in
theorem colimit_ι_cylinderSectionsComparison (W : Opens (S.obj (op i0)))
    [HasColimit (cylinderSections S i0 W)] (i : Set.Ici i0) :
    colimit.ι (cylinderSections S i0 W) i ≫ cylinderSectionsComparison S i0 m W =
      SheafedSpace.Γ.map ((restrictedCone S i0 m W).π.app (op i)).op ≫
        eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m W)) := by
  exact colimit.ι_desc (cylinderSectionsCocone S i0 m W) i

omit [IsDirectedOrder ι] in
private theorem coneComponent_eq_named (W : Opens (S.obj (op i0)))
    (i : Set.Ici i0) :
    coneComponent S i0 m W i = SheafedSpace.restrictOnNamedPreimage
      (m.π.app (op i.1)) (stageOpen S i0 W i)
      (coneOpen S i0 m W) (coneOpen_eq_stage S i0 m W i) := by
  haveI : Mono ((S.obj (op i.1)).ofRestrict
      (stageOpen S i0 W i).isOpenEmbedding) := inferInstance
  apply (cancel_mono ((S.obj (op i.1)).ofRestrict
    (stageOpen S i0 W i).isOpenEmbedding)).1
  exact (coneComponent_fac S i0 m W i).trans
    (SheafedSpace.restrictOnNamedPreimage_fac
      (m.π.app (op i.1)) (stageOpen S i0 W i)
      (coneOpen S i0 m W) (coneOpen_eq_stage S i0 m W i)).symm

omit [IsDirectedOrder ι] in
/-- The coprojection and the original projection agree after both transports. -/
theorem originalStage_cylinderSectionsComparison (W : Opens (S.obj (op i0)))
    [HasColimit (cylinderSections S i0 W)] (i : Set.Ici i0) :
    eqToHom (SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 W i)).symm ≫
      colimit.ι (cylinderSections S i0 W) i ≫ cylinderSectionsComparison S i0 m W =
    (m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 W i)) ≫
      eqToHom (congrArg
        (fun O : Opens m.pt => m.pt.presheaf.obj (op O))
        (coneOpen_eq_stage S i0 m W i).symm) := by
  rw [colimit_ι_cylinderSectionsComparison]
  change eqToHom (SheafedSpace.restrict_Γ_obj
      (S.obj (op i.1)) (stageOpen S i0 W i)).symm ≫
    SheafedSpace.Γ.map (coneComponent S i0 m W i).op ≫
      eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m W)) = _
  rw [coneComponent_eq_named S i0 m W i]
  exact SheafedSpace.restrictOnNamedPreimage_Γ_map
    (m.π.app (op i.1)) (stageOpen S i0 W i)
    (coneOpen S i0 m W) (coneOpen_eq_stage S i0 m W i)

omit [IsDirectedOrder ι] in
/-- Pullback of an open preserves inclusion in the original cone point. -/
theorem coneOpen_mono {U V : Opens (S.obj (op i0))} (h : U ≤ V) :
    coneOpen S i0 m U ≤ coneOpen S i0 m V := by
  have hU := coneOpen_eq_stage S i0 m U (⟨i0, le_refl i0⟩ : Set.Ici i0)
  have hV := coneOpen_eq_stage S i0 m V (⟨i0, le_refl i0⟩ : Set.Ici i0)
  rw [stageOpen_base S i0 U] at hU
  rw [stageOpen_base S i0 V] at hV
  rw [hU, hV]
  exact leOfHom ((Opens.map (m.π.app (op i0)).hom.base).map (homOfLE h))

omit [IsDirectedOrder ι] in
/-- At the base stage the cone's named open is its literal inverse image. -/
theorem coneOpen_base (W : Opens (S.obj (op i0))) :
    coneOpen S i0 m W = (Opens.map (m.π.app (op i0)).hom.base).obj W := by
  simpa only [stageOpen_base S i0 W] using
    coneOpen_eq_stage S i0 m W (⟨i0, le_refl i0⟩ : Set.Ici i0)

variable [∀ W : Opens (S.obj (op i0)), HasColimit (cylinderSections S i0 W)]

/-- The presheaf of colimits of literal restricted-stage sections. -/
@[expose] def cylinderSectionsPresheaf : (Opens (S.obj (op i0)))ᵒᵖ ⥤ C where
  obj U := colimit (cylinderSections S i0 (unop U))
  map := by
    intro U V f
    exact colimMap (stageSectionsRestriction S i0 (unop V) (unop U) (leOfHom f.unop))
  map_id := by
    intro U
    change colimMap (stageSectionsRestriction S i0 (unop U) (unop U) (le_refl _)) = 𝟙 _
    rw [stageSectionsRestriction_id]
    apply colimit.hom_ext
    intro k
    simp only [ι_colimMap, NatTrans.id_app, Category.id_comp, Category.comp_id]
  map_comp := by
    intro U V W f g
    apply colimit.hom_ext
    intro k
    simp only [ι_colimMap, ι_colimMap_assoc]
    have hcomp := congrArg
      (fun η => η.app k ≫ colimit.ι (cylinderSections S i0 (unop W)) k)
      (stageSectionsRestriction_comp S i0 (unop W) (unop V) (unop U)
        (leOfHom g.unop) (leOfHom f.unop))
    simpa only [NatTrans.comp_app, Category.assoc] using hcomp.symm

omit [IsDirectedOrder ι] in
/-- The generic open-restriction square at an actual inclusion of opens. -/
theorem cylinderSectionsComparison_restrict (U V : Opens (S.obj (op i0)))
    (h : U ≤ V) :
    colimMap (stageSectionsRestriction S i0 U V h) ≫
      cylinderSectionsComparison S i0 m U =
    cylinderSectionsComparison S i0 m V ≫
      m.pt.presheaf.map (homOfLE (coneOpen_mono S i0 m h)).op := by
  apply colimit.hom_ext
  intro i
  haveI : Epi (eqToHom (SheafedSpace.restrict_Γ_obj
      (S.obj (op i.1)) (stageOpen S i0 V i)).symm) := inferInstance
  apply (cancel_epi (eqToHom (SheafedSpace.restrict_Γ_obj
    (S.obj (op i.1)) (stageOpen S i0 V i)).symm)).1
  simp only [ι_colimMap_assoc]
  have hn := namedSectionRestriction_naturality
    (m.π.app (op i.1)) (stageOpen_mono S i0 h i)
    (coneOpen_eq_stage S i0 m U i) (coneOpen_eq_stage S i0 m V i)
    (coneOpen_mono S i0 m h)
  simp only [stageSectionsRestriction, stageSectionRestriction, Category.assoc]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]
  simp only [Category.assoc, originalStage_cylinderSectionsComparison]
  simpa only [Functor.const_obj_obj] using hn.symm

/-- The comparison is a natural transformation on all base opens. -/
@[expose] def cylinderSectionsNaturality :
    cylinderSectionsPresheaf S i0 ⟶
      (Opens.map (m.π.app (op i0)).hom.base).op ⋙ m.pt.presheaf where
  app U := cylinderSectionsComparison S i0 m (unop U) ≫
    eqToHom (congrArg (fun O : Opens m.pt => m.pt.presheaf.obj (op O))
      (coneOpen_base S i0 m (unop U)))
  naturality := by
    intro U V f
    have hsquare := cylinderSectionsComparison_restrict S i0 m
      (unop V) (unop U) (leOfHom f.unop)
    change colimMap (stageSectionsRestriction S i0 (unop V) (unop U)
        (leOfHom f.unop)) ≫
      (cylinderSectionsComparison S i0 m (unop V) ≫
        eqToHom (congrArg (fun O : Opens m.pt => m.pt.presheaf.obj (op O))
          (coneOpen_base S i0 m (unop V)))) =
      (cylinderSectionsComparison S i0 m (unop U) ≫
        eqToHom (congrArg (fun O : Opens m.pt => m.pt.presheaf.obj (op O))
          (coneOpen_base S i0 m (unop U)))) ≫
        m.pt.presheaf.map (((Opens.map (m.π.app (op i0)).hom.base).op).map f)
    rw [← Category.assoc, hsquare]
    simp only [Category.assoc]
    congr 1
    let htarget := leOfHom ((Opens.map (m.π.app (op i0)).hom.base).map f.unop)
    have hmap : (Opens.map (m.π.app (op i0)).hom.base).op.map f =
        (homOfLE htarget).op := Subsingleton.elim _ _
    rw [hmap]
    exact presheaf_cast_restrict m.pt
      (coneOpen_base S i0 m (unop V)) (coneOpen_base S i0 m (unop U))
      (coneOpen_mono S i0 m (leOfHom f.unop)) htarget

omit [IsDirectedOrder ι] in
/-- The official ring pointwise comparison is the generic comparison. -/
theorem ringCylinderSectionsComparison_eq
    (R : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} CommRingCat.{v})
    (i : ι) (cone : Cone R) (W : Opens (R.obj (op i))) :
    nativeCommRingCylinderSectionsComparison R i cone W =
      cylinderSectionsComparison R i cone W := by
  apply colimit.hom_ext
  intro k
  rw [colimit_ι_nativeCommRingCylinderSectionsComparison,
    colimit_ι_cylinderSectionsComparison]

omit [IsDirectedOrder ι] in
/-- The official additive pointwise comparison is the generic comparison. -/
theorem additiveCylinderSectionsComparison_eq
    (A : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v})
    (i : ι) (cone : Cone A) (W : Opens (A.obj (op i))) :
    nativeAdditiveCylinderSectionsComparison A i cone W =
      cylinderSectionsComparison A i cone W := by
  apply colimit.hom_ext
  intro k
  rw [colimit_ι_nativeAdditiveCylinderSectionsComparison,
    colimit_ι_cylinderSectionsComparison]

omit [IsDirectedOrder ι] in
/-- Ring-cylinder comparisons respect all inclusions of base opens. -/
theorem ringCylinderSectionsComparison_restrict
    (R : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} CommRingCat.{v})
    (i : ι) (cone : Cone R) (U V : Opens (R.obj (op i))) (h : U ≤ V) :
    colimMap (stageSectionsRestriction R i U V h) ≫
        nativeCommRingCylinderSectionsComparison R i cone U =
      nativeCommRingCylinderSectionsComparison R i cone V ≫
        cone.pt.presheaf.map (homOfLE (coneOpen_mono R i cone h)).op := by
  letI : ∀ W : Opens (R.obj (op i)), HasColimit (cylinderSections R i W) :=
    fun _ => inferInstance
  rw [ringCylinderSectionsComparison_eq R i cone U,
    ringCylinderSectionsComparison_eq R i cone V]
  exact cylinderSectionsComparison_restrict R i cone U V h

omit [IsDirectedOrder ι] in
/-- Additive-cylinder comparisons respect all inclusions of base opens. -/
theorem additiveCylinderSectionsComparison_restrict
    (A : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v})
    (i : ι) (cone : Cone A) (U V : Opens (A.obj (op i))) (h : U ≤ V) :
    colimMap (stageSectionsRestriction A i U V h) ≫
        nativeAdditiveCylinderSectionsComparison A i cone U =
      nativeAdditiveCylinderSectionsComparison A i cone V ≫
        cone.pt.presheaf.map (homOfLE (coneOpen_mono A i cone h)).op := by
  letI : ∀ W : Opens (A.obj (op i)), HasColimit (cylinderSections A i W) :=
    fun _ => inferInstance
  rw [additiveCylinderSectionsComparison_eq A i cone U,
    additiveCylinderSectionsComparison_eq A i cone V]
  exact cylinderSectionsComparison_restrict A i cone U V h

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
