/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# Inverse image of a module presheaf along a continuous map

The neighborhood-colimit ring acts on the neighborhood-colimit additive presheaf.
The action and restriction maps are those of the actual pointwise left Kan extensions;
the underlying additive presheaf is naturally the usual inverse image.

## References

* Mathlib, `Mathlib/Algebra/Category/ModuleCat/Presheaf/ColimitFunctor.lean`
  (Joël Riou): the varying-ring module-colimit action transported to the
  neighborhood-colimit pointwise Kan extensions.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
  draft), §2.7.2 (p. 93) and Exercise 7.2.D(b,e) (p. 205): the temporary
  inverse-image presheaf motivates this prerequisite. The simultaneous
  coefficient/element colimit construction works even for `RingCat` presheaves
  of noncommutative rings; it is not the full sheafified pullback requested there.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- Open neighborhoods of the image of `U`, ordered in the colimit direction. -/
abbrev index (U : Opens X) :=
  CostructuredArrow (Opens.map f).op (op U)

/-- A common refinement of two neighborhoods. -/
private def meetIndex {U : Opens X} (i j : index f U) : index f U :=
  CostructuredArrow.mk <| (homOfLE (show U ≤
    (Opens.map f).obj (unop i.left ⊓ unop j.left) from
    le_inf (leOfHom i.hom.unop) (leOfHom j.hom.unop))).op

/-- Restriction from the first neighborhood to the common refinement. -/
private def meetLeft {U : Opens X} (i j : index f U) : i ⟶ meetIndex f i j :=
  CostructuredArrow.homMk (homOfLE inf_le_left).op

/-- Restriction from the second neighborhood to the common refinement. -/
private def meetRight {U : Opens X} (i j : index f U) : j ⟶ meetIndex f i j :=
  CostructuredArrow.homMk (homOfLE inf_le_right).op

private instance {U : Opens X} : IsFiltered (index f U) where
  nonempty := ⟨CostructuredArrow.mk <| (homOfLE (show U ≤ (Opens.map f).obj ⊤ from
    by rw [Opens.map_top]; exact le_top)).op⟩
  cocone_objs i j := ⟨meetIndex f i j, meetLeft f i j, meetRight f i j, trivial⟩
  cocone_maps {i j} α β := ⟨j, 𝟙 _, by
    apply CostructuredArrow.hom_ext
    apply Subsingleton.elim⟩

/-- The neighborhood diagram of sections, with the opposite orientation expected by modules. -/
private abbrev indexProj (U : Opens X) : ((index f U)ᵒᵖ)ᵒᵖ ⥤ (Opens Y)ᵒᵖ :=
  unopUnop (index f U) ⋙ CostructuredArrow.proj (Opens.map f).op (op U)

/-- Ring sections over neighborhoods of `f(U)`. -/
private abbrev indexedRing (R : Y.Presheaf RingCat.{v}) (U : Opens X) :
    ((index f U)ᵒᵖ)ᵒᵖ ⥤ RingCat.{v} := indexProj f U ⋙ R

/-- The module sections over the same neighborhoods as their ring coefficients. -/
private noncomputable def indexedModule (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (U : Opens X) :
    PresheafOfModules.{v} (indexedRing f R U) where
  obj i := M.obj ((indexProj f U).obj i)
  map φ := M.map ((indexProj f U).map φ)

private instance (U : Opens X) : InitiallySmall.{v} ((index f U)ᵒᵖ) :=
  InitiallySmall.mk' (𝟭 ((index f U)ᵒᵖ))

/-- The native module-colimit ring is the pointwise Kan colimit ring. -/
private noncomputable def ringIso (R : Y.Presheaf RingCat.{v}) (U : Opens X) :
    colimit (indexedRing f R U) ≅
      ((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U) :=
  Functor.Final.colimitIso (unopUnop (index f U))
    (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R)

/-- The native module-colimit group is the pointwise Kan colimit group. -/
private noncomputable def groupIso (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (U : Opens X) :
    colimit (indexedModule f R M U).presheaf ≅
      ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U) :=
  Functor.Final.colimitIso (unopUnop (index f U))
    (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf)

private theorem ringGenerator (R : Y.Presheaf RingCat.{v}) (U : Opens X)
    (i : index f U) (a : R.obj i.left) :
    (ringIso f R U).hom ((colimit.ι (indexedRing f R U) (op (op i))) a) =
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R) i) a := by
  exact ConcreteCategory.congr_hom
    (Functor.Final.ι_colimitIso_hom (unopUnop (index f U))
      (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R) (op (op i))) a

private theorem groupGenerator (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (U : Opens X)
    (i : index f U) (x : M.obj i.left) :
    (groupIso f R M U).hom
      ((colimit.ι (indexedModule f R M U).presheaf (op (op i))) x) =
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) x := by
  exact ConcreteCategory.congr_hom
    (Functor.Final.ι_colimitIso_hom (unopUnop (index f U))
      (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) (op (op i))) x

private noncomputable instance indexedModuleAction (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (U : Opens X) :
    Module (colimit (indexedRing f R U) : RingCat.{v})
      (PresheafOfModules.ModuleColimit
        (colimit.isColimit (indexedRing f R U))
        (colimit.isColimit (indexedModule f R M U).presheaf)) :=
  PresheafOfModules.ModuleColimit.instModuleCarrierPtOppositeRingCat
    (colimit.isColimit (indexedRing f R U))
    (colimit.isColimit (indexedModule f R M U).presheaf)

@[instance_reducible] private noncomputable def oldPointwiseModule (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (U : Opens X) :
    Module
      (((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U))
      (((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) := by
  let hcR := colimit.isColimit (indexedRing f R U)
  let hcM := colimit.isColimit (indexedModule f R M U).presheaf
  let nativeModule : Module (colimit (indexedRing f R U) : RingCat.{v})
      (colimit (indexedModule f R M U).presheaf : AddCommGrpCat.{v}) :=
    PresheafOfModules.ModuleColimit.instModuleCarrierPtOppositeRingCat hcR hcM
  letI : Module (colimit (indexedRing f R U) : RingCat.{v})
      (((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) :=
    AddEquiv.module _ (groupIso f R M U).symm.addCommGroupIsoToAddEquiv
  exact Module.compHom _ (ringIso f R U).symm.ringCatIsoToRingEquiv.toRingHom

noncomputable instance pointwiseModule (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (U : Opens X) :
    Module
      (((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U))
      (((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) := by
  letI : IsFiltered (index f U) :=
    { nonempty := ⟨CostructuredArrow.mk <| (homOfLE (show U ≤ (Opens.map f).obj ⊤ from
        by rw [Opens.map_top]; exact le_top)).op⟩
      cocone_objs i j :=
        ⟨CostructuredArrow.mk <| (homOfLE (show U ≤
            (Opens.map f).obj (unop i.left ⊓ unop j.left) from
            le_inf (leOfHom i.hom.unop) (leOfHom j.hom.unop))).op,
          CostructuredArrow.homMk (homOfLE inf_le_left).op,
          CostructuredArrow.homMk (homOfLE inf_le_right).op, trivial⟩
      cocone_maps := fun {_ _} _ _ => ⟨_, 𝟙 _, by
        apply CostructuredArrow.hom_ext
        apply Subsingleton.elim⟩ }
  letI : InitiallySmall.{v} ((index f U)ᵒᵖ) :=
    InitiallySmall.mk' (𝟭 ((index f U)ᵒᵖ))
  let neighborhood : ((index f U)ᵒᵖ)ᵒᵖ ⥤ (Opens Y)ᵒᵖ :=
    unopUnop (index f U) ⋙ CostructuredArrow.proj (Opens.map f).op (op U)
  let ringDiagram : ((index f U)ᵒᵖ)ᵒᵖ ⥤ RingCat.{v} := neighborhood ⋙ R
  let moduleDiagram : PresheafOfModules.{v} ringDiagram :=
    { obj i := M.obj (neighborhood.obj i)
      map φ := M.map (neighborhood.map φ) }
  let ringComparison : colimit ringDiagram ≅
      ((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U) :=
    Functor.Final.colimitIso (unopUnop (index f U))
      (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R)
  let groupComparison : colimit moduleDiagram.presheaf ≅
      ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U) :=
    Functor.Final.colimitIso (unopUnop (index f U))
      (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf)
  let hcR := colimit.isColimit ringDiagram
  let hcM := colimit.isColimit moduleDiagram.presheaf
  let nativeModule : Module (colimit ringDiagram : RingCat.{v})
      (colimit moduleDiagram.presheaf : AddCommGrpCat.{v}) :=
    PresheafOfModules.ModuleColimit.instModuleCarrierPtOppositeRingCat hcR hcM
  letI : Module (colimit ringDiagram : RingCat.{v})
      (((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) :=
    AddEquiv.module _ groupComparison.symm.addCommGroupIsoToAddEquiv
  exact Module.compHom _ ringComparison.symm.ringCatIsoToRingEquiv.toRingHom

private theorem pointwiseModule_eq_old (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (U : Opens X) :
    pointwiseModule f R M U = oldPointwiseModule f R M U := rfl

theorem pointwise_smul_ι (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (U : Opens X) (i : index f U)
    (r : R.obj i.left) (m : M.obj i.left) :
    letI : Module
      (colimit (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R) : RingCat.{v})
      (colimit (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) : AddCommGrpCat.{v}) :=
      pointwiseModule f R M U
    (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) (r • m) =
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R) i) r •
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) m := by
  let hcR := colimit.isColimit (indexedRing f R U)
  let hcM := colimit.isColimit (indexedModule f R M U).presheaf
  have hs (a : ↑(colimit (indexedRing f R U) : RingCat.{v}))
      (b : PresheafOfModules.ModuleColimit hcR hcM) :
      (groupIso f R M U).hom (a • b) =
        (ringIso f R U).hom a • (groupIso f R M U).hom b := by
    change _ = (groupIso f R M U).hom
      ((ringIso f R U).inv ((ringIso f R U).hom a) •
       (show PresheafOfModules.ModuleColimit hcR hcM from
         (groupIso f R M U).inv ((groupIso f R M U).hom b)))
    rw [(ringIso f R U).hom_inv_id_apply]
    have hb : (groupIso f R M U).inv ((groupIso f R M U).hom b) = b :=
      (groupIso f R M U).hom_inv_id_apply b
    rw [hb]
  let d : ((index f U)ᵒᵖ)ᵒᵖ := op (op i)
  have h := congrArg (groupIso f R M U).hom
    (PresheafOfModules.ModuleColimit.smul_eq hcR hcM (U := d) r m)
  rw [hs] at h
  dsimp only [PresheafOfModules.ModuleColimit.ιM, PresheafOfModules.ModuleColimit.ιR] at h
  erw [ringGenerator f R U i, groupGenerator f R M U i,
    groupGenerator f R M U i] at h
  exact h.symm

theorem ring_map_ι (R : Y.Presheaf RingCat.{v})
    {U V : Opens X} (g : op U ⟶ op V) (i : index f U) (r : R.obj i.left) :
    ((Opens.map f).op.pointwiseLeftKanExtension R).map g
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R) i) r) =
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op V) ⋙ R)
        ((CostructuredArrow.map g).obj i)) r := by
  change (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R) i ≫
    ((Opens.map f).op.pointwiseLeftKanExtension R).map g).hom r = _
  erw [Functor.pointwiseLeftKanExtension_map, colimit.ι_desc]
  rfl

theorem group_map_ι (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) {U V : Opens X}
    (g : op U ⟶ op V) (i : index f U) (m : M.obj i.left) :
    ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).map g
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) m) =
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op V) ⋙ M.presheaf)
        ((CostructuredArrow.map g).obj i)) m := by
  change (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i ≫
    ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).map g).hom m = _
  erw [Functor.pointwiseLeftKanExtension_map, colimit.ι_desc]
  rfl

theorem pointwise_jointly_surjective (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (U : Opens X)
    (r : ((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U))
    (m : ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) :
    ∃ (i : index f U) (a : R.obj i.left) (b : M.obj i.left),
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R) i) a = r ∧
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) b = m := by
  let hcR := colimit.isColimit (indexedRing f R U)
  let hcM := colimit.isColimit (indexedModule f R M U).presheaf
  obtain ⟨j, a, b, ha, hb⟩ :=
    PresheafOfModules.ModuleColimit.jointly_surjective₂
      (hcR := hcR) (hcM := hcM)
        ((ringIso f R U).inv r) ((groupIso f R M U).inv m)
  refine ⟨unop (unop j), a, b, ?_, ?_⟩
  · rw [← ringGenerator f R U (unop (unop j))]
    erw [ha]
    exact (ringIso f R U).inv_hom_id_apply r
  · erw [← groupGenerator f R M U (unop (unop j))]
    erw [hb]
    exact (groupIso f R M U).inv_hom_id_apply m

theorem restriction_smul (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) {U V : Opens X} (g : op U ⟶ op V)
    (r : ((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U))
    (m : ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) :
    letI := pointwiseModule f R M U
    letI := pointwiseModule f R M V
    ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).map g (r • m) =
      (((Opens.map f).op.pointwiseLeftKanExtension R).map g r) •
      (((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).map g m) := by
  obtain ⟨i, a, b, ha, hb⟩ := pointwise_jointly_surjective f R M U r m
  erw [← ha, ← hb]
  erw [← pointwise_smul_ι f R M U i a b]
  erw [group_map_ι f R M g i (a • b), ring_map_ι f R g i a,
    group_map_ι f R M g i b]
  exact pointwise_smul_ι f R M V ((CostructuredArrow.map g).obj i) a b

/-- The ordinary inverse-image additive presheaf equipped with its neighborhood-colimit action. -/
noncomputable def inverseImageModule (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) :
    PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R) :=
  letI (U : (Opens X)ᵒᵖ) : Module
      (((Opens.map f).op.pointwiseLeftKanExtension R).obj U)
      (((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj U) :=
    pointwiseModule f R M (unop U)
  PresheafOfModules.ofPresheaf
    ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf)
    (fun {_U _V} g r m => restriction_smul f R M g r m)

/-- Compare a pointwise Kan extension to the chosen presheaf inverse image. -/
noncomputable def pointwiseToPullback
    (C : Type (v + 1)) [Category.{v} C] [HasColimits C]
    (F : Y.Presheaf C) :
    (Opens.map f).op.pointwiseLeftKanExtension F ≅
      (TopCat.Presheaf.pullback C f).obj F :=
  Functor.leftKanExtensionUnique
    ((Opens.map f).op.pointwiseLeftKanExtension F)
    ((Opens.map f).op.pointwiseLeftKanExtensionUnit F)
    ((Opens.map f).op.leftKanExtension F)
    ((Opens.map f).op.leftKanExtensionUnit F)

/-- Apply an input module morphism on each Kan-colimit generator. -/
noncomputable def pointwiseMap {R : Y.Presheaf RingCat.{v}}
    {M N : PresheafOfModules.{v} R} (φ : M ⟶ N) :
    (Opens.map f).op.pointwiseLeftKanExtension M.presheaf ⟶
      (Opens.map f).op.pointwiseLeftKanExtension N.presheaf where
  app U := colim.map (Functor.whiskerLeft
    (CostructuredArrow.proj (Opens.map f).op U)
    ((PresheafOfModules.toPresheaf R).map φ))
  naturality U V g := by
    apply colimit.hom_ext
    intro i
    simp only [Functor.pointwiseLeftKanExtension_map]
    erw [colimit.ι_desc_assoc]
    erw [colimit.ι_map]
    erw [colimit.ι_map_assoc]
    erw [colimit.ι_desc]
    rfl

theorem pointwiseMap_ι {R : Y.Presheaf RingCat.{v}}
    {M N : PresheafOfModules.{v} R} (φ : M ⟶ N)
    (U : Opens X) (i : index f U) (m : M.obj i.left) :
    (pointwiseMap f φ).app (op U)
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) m) =
    (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ N.presheaf) i)
      (φ.app i.left m) := by
  change (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i ≫
    (pointwiseMap f φ).app (op U)).hom m = _
  erw [colimit.ι_map]
  rfl

theorem pointwiseMap_smul {R : Y.Presheaf RingCat.{v}}
    {M N : PresheafOfModules.{v} R} (φ : M ⟶ N) (U : Opens X)
    (r : ((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U))
    (m : ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) :
    letI := pointwiseModule f R M U
    letI := pointwiseModule f R N U
    (pointwiseMap f φ).app (op U) (r • m) =
      r • (pointwiseMap f φ).app (op U) m := by
  obtain ⟨i, a, b, ha, hb⟩ := pointwise_jointly_surjective f R M U r m
  erw [← ha, ← hb]
  erw [← pointwise_smul_ι f R M U i a b]
  erw [pointwiseMap_ι f φ U i (a • b), pointwiseMap_ι f φ U i b]
  rw [map_smul, pointwise_smul_ι f R N U i]
  rfl

/-- The module-linear map induced on ordinary presheaf inverse images. -/
noncomputable def inverseImageMap {R : Y.Presheaf RingCat.{v}}
    {M N : PresheafOfModules.{v} R} (φ : M ⟶ N) :
    inverseImageModule f R M ⟶ inverseImageModule f R N :=
  PresheafOfModules.homMk (pointwiseMap f φ)
    (fun U r m => pointwiseMap_smul f φ (unop U) r m)

theorem pointwiseMap_id (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) :
    pointwiseMap f (𝟙 M) =
      𝟙 ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf) := by
  apply NatTrans.ext
  funext U
  change colim.map (Functor.whiskerLeft
    (CostructuredArrow.proj (Opens.map f).op U)
    ((PresheafOfModules.toPresheaf R).map (𝟙 M))) = 𝟙 _
  erw [(PresheafOfModules.toPresheaf R).map_id M]
  erw [Functor.whiskerLeft_id]
  exact (colim (J := index f (unop U)) (C := AddCommGrpCat.{v})).map_id _

theorem pointwiseMap_comp (R : Y.Presheaf RingCat.{v})
    {M N P : PresheafOfModules.{v} R} (φ : M ⟶ N) (ψ : N ⟶ P) :
    pointwiseMap f (φ ≫ ψ) = pointwiseMap f φ ≫ pointwiseMap f ψ := by
  apply NatTrans.ext
  funext U
  change colim.map (Functor.whiskerLeft
    (CostructuredArrow.proj (Opens.map f).op U)
    ((PresheafOfModules.toPresheaf R).map (φ ≫ ψ))) =
      colim.map (Functor.whiskerLeft
        (CostructuredArrow.proj (Opens.map f).op U)
        ((PresheafOfModules.toPresheaf R).map φ)) ≫
      colim.map (Functor.whiskerLeft
        (CostructuredArrow.proj (Opens.map f).op U)
        ((PresheafOfModules.toPresheaf R).map ψ))
  exact
    (colim (J := index f (unop U)) (C := AddCommGrpCat.{v})).map_comp
      ((CostructuredArrow.proj (Opens.map f).op U).whiskerLeft
        ((PresheafOfModules.toPresheaf R).map φ))
      ((CostructuredArrow.proj (Opens.map f).op U).whiskerLeft
        ((PresheafOfModules.toPresheaf R).map ψ))

/-- Ordinary inverse image as a functor on presheaves of modules. -/
noncomputable def inverseImageFunctor (R : Y.Presheaf RingCat.{v}) :
    PresheafOfModules.{v} R ⥤
      PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R) where
  obj M := inverseImageModule f R M
  map φ := inverseImageMap f φ
  map_id M := by
    apply (PresheafOfModules.toPresheaf _).map_injective
    exact pointwiseMap_id f R M
  map_comp φ ψ := by
    apply (PresheafOfModules.toPresheaf _).map_injective
    exact pointwiseMap_comp f R φ ψ

theorem pointwiseMap_unit {R : Y.Presheaf RingCat.{v}}
    {M N : PresheafOfModules.{v} R} (φ : M ⟶ N) :
    (Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf ≫
      (Opens.map f).op.whiskerLeft (pointwiseMap f φ) =
    (PresheafOfModules.toPresheaf R).map φ ≫
      (Opens.map f).op.pointwiseLeftKanExtensionUnit N.presheaf := by
  apply NatTrans.ext
  funext U
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.pointwiseLeftKanExtensionUnit_app, pointwiseMap]
  erw [colimit.ι_map]
  rfl

theorem pointwiseToPullback_fac (F : Y.Presheaf AddCommGrpCat.{v}) :
    (Opens.map f).op.pointwiseLeftKanExtensionUnit F ≫
      (Opens.map f).op.whiskerLeft (pointwiseToPullback f AddCommGrpCat.{v} F).hom =
    (Opens.map f).op.leftKanExtensionUnit F := by
  exact
    (Functor.descOfIsLeftKanExtension_fac
      (α := (Opens.map f).op.pointwiseLeftKanExtensionUnit F)
      (G := (Opens.map f).op.leftKanExtension F)
      (β := (Opens.map f).op.leftKanExtensionUnit F))

/-- The pointwise scalar operation, with its module instance explicitly selected. -/
noncomputable def pointwiseSmul (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (U : Opens X)
    (r : ((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U))
    (m : ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) :
    ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U) := by
  letI := pointwiseModule f R M U
  exact r • m

theorem pointwiseSmul_eq (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (U : Opens X)
    (i : index f U) (r : R.obj i.left) (m : M.obj i.left) :
    pointwiseSmul f R M U
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R) i) r)
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) m) =
    (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i)
      (r • m) :=
  (pointwise_smul_ι f R M U i r m).symm

theorem unit_smul (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (V : (Opens Y)ᵒᵖ)
    (r : R.obj V) (m : M.obj V) :
    pointwiseSmul f R M ((Opens.map f).obj (unop V))
      (((Opens.map f).op.pointwiseLeftKanExtensionUnit R).app V r)
      (((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V m) =
    ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V (r • m) := by
  exact pointwiseSmul_eq f R M ((Opens.map f).obj (unop V))
    (CostructuredArrow.mk (𝟙 ((Opens.map f).op.obj V))) r m

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary additive presheaf inverse image is naturally the underlying functor. -/
noncomputable def underlyingComparison (R : Y.Presheaf RingCat.{v}) :
    inverseImageFunctor f R ⋙
        PresheafOfModules.toPresheaf
          ((Opens.map f).op.pointwiseLeftKanExtension R) ≅
      PresheafOfModules.toPresheaf R ⋙
        TopCat.Presheaf.pullback AddCommGrpCat.{v} f :=
  NatIso.ofComponents (fun M => pointwiseToPullback f AddCommGrpCat.{v} M.presheaf)
    (fun {M N} φ => by
      change pointwiseMap f φ ≫ (pointwiseToPullback f AddCommGrpCat.{v} N.presheaf).hom =
        (pointwiseToPullback f AddCommGrpCat.{v} M.presheaf).hom ≫
          ((Opens.map f).op.lan).map ((PresheafOfModules.toPresheaf R).map φ)
      apply ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).hom_ext_of_isLeftKanExtension
        ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf)
      rw [Functor.whiskerLeft_comp]
      rw [← Category.assoc, pointwiseMap_unit f φ]
      let L := (Opens.map f).op
      let η : M.presheaf ⟶ N.presheaf := (PresheafOfModules.toPresheaf R).map φ
      change (η ≫ L.pointwiseLeftKanExtensionUnit N.presheaf) ≫
          L.whiskerLeft (pointwiseToPullback f AddCommGrpCat.{v} N.presheaf).hom =
        L.pointwiseLeftKanExtensionUnit M.presheaf ≫
          L.whiskerLeft ((pointwiseToPullback f AddCommGrpCat.{v} M.presheaf).hom ≫
            L.lan.map η)
      rw [Category.assoc, pointwiseToPullback_fac f N.presheaf]
      dsimp only [L]
      simp only [Functor.whiskerLeft_comp, ← Category.assoc,
        pointwiseToPullback_fac f M.presheaf]
      exact (Opens.map f).op.lanUnit.naturality η)


end RingedSpaces.Modules.PresheafInverseImage
