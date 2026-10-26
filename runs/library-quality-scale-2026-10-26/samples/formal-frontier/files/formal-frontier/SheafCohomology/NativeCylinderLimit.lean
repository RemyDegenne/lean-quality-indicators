/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module
public import SheafCohomology.NativeOpenRestriction
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final

public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Native limits of principal-tail open cylinders

The inverse-image opens in a directed opposite diagram of sheafed spaces form
an actual functor of native restrictions. Restricting an arbitrary native limit
cone to the inverse image of its distinguished-stage open gives a native limit
cone over that functor.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]

/-- Inclusion of a principal tail in a directed preorder. -/
@[expose] def tailInclusion (i0 : ι) : Set.Ici i0 ⥤ ι :=
  (Subtype.mono_coe (· ∈ Set.Ici i0)).functor

private instance tailDirected (i0 : ι) : IsDirectedOrder (Set.Ici i0) :=
  ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.1 j.1
    exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩⟩

/-- The principal tail of a directed preorder is directed. -/
theorem tailDirectedOrder (i0 : ι) : IsDirectedOrder (Set.Ici i0) :=
  tailDirected i0

/-- A principal tail is final even without a linear order. -/
instance tailInclusion_final (i0 : ι) : (tailInclusion i0).Final := by
  change (Subtype.mono_coe (· ∈ Set.Ici i0)).functor.Final
  rw [Monotone.final_functor_iff]
  intro i
  obtain ⟨j, hi0j, hij⟩ := exists_ge_ge i0 i
  exact ⟨⟨j, hi0j⟩, hij⟩

instance tailInclusion_op_initial (i0 : ι) : (tailInclusion i0).op.Initial :=
  inferInstance

variable {C : Type (v + 1)} [Category.{v} C]
variable (N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C) (i0 : ι)

/-- The original diagram, restricted to the opposite principal tail. -/
abbrev tailDiagram : (Set.Ici i0)ᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C :=
  (tailInclusion i0).op ⋙ N

/-- Transition from a tail stage to the distinguished stage. -/
def transition (i : Set.Ici i0) : N.obj (op i.1) ⟶ N.obj (op i0) :=
  N.map (homOfLE i.property).op

/-- The inverse-image open of the distinguished open at each tail stage. -/
def stageOpen (U0 : Opens (N.obj (op i0))) (i : Set.Ici i0) : Opens (N.obj (op i.1)) :=
  (Opens.map (transition N i0 i).hom.base).obj U0

omit [IsDirectedOrder ι] in
theorem transition_map {i j : (Set.Ici i0)ᵒᵖ} (f : i ⟶ j) :
    (tailDiagram N i0).map f ≫ transition N i0 (unop j) =
      transition N i0 (unop i) := by
  unfold tailDiagram transition
  rw [Functor.comp_map, ← N.map_comp]
  exact congrArg N.map (Subsingleton.elim _ _)

omit [IsDirectedOrder ι] in
/-- The named source open is exactly the inverse image of the target open. -/
theorem stageOpen_map (U0 : Opens (N.obj (op i0)))
    {i j : (Set.Ici i0)ᵒᵖ} (f : i ⟶ j) :
    stageOpen N i0 U0 (unop i) =
      (Opens.map ((tailDiagram N i0).map f).hom.base).obj
        (stageOpen N i0 U0 (unop j)) := by
  calc
    stageOpen N i0 U0 (unop i) =
        (Opens.map (((tailDiagram N i0).map f ≫
          transition N i0 (unop j)).hom.base)).obj U0 := by
            change (Opens.map (transition N i0 (unop i)).hom.base).obj U0 = _
            rw [transition_map N i0 f]
    _ = (Opens.map ((tailDiagram N i0).map f).hom.base).obj
          (stageOpen N i0 U0 (unop j)) := by
            rw [comp_hom_base, Opens.map_comp_obj]
            rfl

/-- The literal sheafed-space restriction at a tail stage. -/
abbrev stage (U0 : Opens (N.obj (op i0))) (i : (Set.Ici i0)ᵒᵖ) :
    SheafedSpace.{v + 1, v, v} C :=
  (N.obj (op (unop i).1)).restrict (stageOpen N i0 U0 (unop i)).isOpenEmbedding

/-- The native restriction of a transition, including its named-open transport. -/
def stageMap (U0 : Opens (N.obj (op i0)))
    {i j : (Set.Ici i0)ᵒᵖ} (f : i ⟶ j) : stage N i0 U0 i ⟶ stage N i0 U0 j :=
  restrictOnNamedPreimage ((tailDiagram N i0).map f)
    (stageOpen N i0 U0 (unop j)) (stageOpen N i0 U0 (unop i))
    (stageOpen_map N i0 U0 f)

omit [IsDirectedOrder ι] in
theorem stageMap_fac (U0 : Opens (N.obj (op i0)))
    {i j : (Set.Ici i0)ᵒᵖ} (f : i ⟶ j) :
    stageMap N i0 U0 f ≫
      (N.obj (op (unop j).1)).ofRestrict (stageOpen N i0 U0 (unop j)).isOpenEmbedding =
      (N.obj (op (unop i).1)).ofRestrict (stageOpen N i0 U0 (unop i)).isOpenEmbedding ≫
        (tailDiagram N i0).map f :=
  restrictOnNamedPreimage_fac _ _ _ _

/-- The actual opposite-tail functor on restricted native sheafed spaces. -/
@[expose] def restricted (U0 : Opens (N.obj (op i0))) :
    (Set.Ici i0)ᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C where
  obj := stage N i0 U0
  map := fun f => stageMap N i0 U0 f
  map_id := by
    intro i
    apply (cancel_mono ((N.obj (op (unop i).1)).ofRestrict
      (stageOpen N i0 U0 (unop i)).isOpenEmbedding)).1
    rw [stageMap_fac]
    change _ ≫ N.map ((tailInclusion i0).op.map (𝟙 i)) = _
    simp
  map_comp := by
    intro i j k f g
    apply (cancel_mono ((N.obj (op (unop k).1)).ofRestrict
      (stageOpen N i0 U0 (unop k)).isOpenEmbedding)).1
    rw [stageMap_fac, Category.assoc, stageMap_fac,
      ← Category.assoc, stageMap_fac]
    simp only [Functor.map_comp, Category.assoc]

/-- The canonical native inclusions constitute a natural transformation. -/
@[expose] def inclusion (U0 : Opens (N.obj (op i0))) :
    restricted N i0 U0 ⟶ tailDiagram N i0 where
  app i := (N.obj (op (unop i).1)).ofRestrict
    (stageOpen N i0 U0 (unop i)).isOpenEmbedding
  naturality := by
    intro i j f
    exact stageMap_fac N i0 U0 f

/-- The inverse image of the distinguished open in the original cone point. -/
def coneOpen (m : Cone N) (U0 : Opens (N.obj (op i0))) : Opens m.pt :=
  (Opens.map (m.π.app (op i0)).hom.base).obj U0

omit [IsDirectedOrder ι] in
/-- Pulling back the stage open along its actual cone projection recovers the
same open in the cone point. -/
theorem coneOpen_eq_stage (m : Cone N) (U0 : Opens (N.obj (op i0)))
    (i : Set.Ici i0) :
    coneOpen N i0 m U0 =
      (Opens.map (m.π.app (op i.1)).hom.base).obj (stageOpen N i0 U0 i) := by
  have hw := m.w (homOfLE i.property).op
  change m.π.app (op i.1) ≫ transition N i0 i = m.π.app (op i0) at hw
  unfold coneOpen stageOpen
  rw [← hw, comp_hom_base, Opens.map_comp_obj]

/-- The restricted cone component is the named-preimage native arrow. -/
def coneComponent (m : Cone N) (U0 : Opens (N.obj (op i0)))
    (i : Set.Ici i0) :
    m.pt.restrict (coneOpen N i0 m U0).isOpenEmbedding ⟶
      stage N i0 U0 (op i) :=
  restrictOnNamedPreimage (m.π.app (op i.1)) (stageOpen N i0 U0 i)
    (coneOpen N i0 m U0) (coneOpen_eq_stage N i0 m U0 i)

omit [IsDirectedOrder ι] in
/-- Each native cone component commutes with the original projection. -/
theorem coneComponent_fac (m : Cone N) (U0 : Opens (N.obj (op i0)))
    (i : Set.Ici i0) :
    coneComponent N i0 m U0 i ≫
      (inclusion N i0 U0).app (op i) =
      m.pt.ofRestrict (coneOpen N i0 m U0).isOpenEmbedding ≫
        m.π.app (op i.1) :=
  restrictOnNamedPreimage_fac _ _ _ _

omit [IsDirectedOrder ι] in
private theorem coneComponent_naturality (m : Cone N) (U0 : Opens (N.obj (op i0)))
    {i j : (Set.Ici i0)ᵒᵖ} (f : i ⟶ j) :
    coneComponent N i0 m U0 (unop i) ≫ stageMap N i0 U0 f =
      coneComponent N i0 m U0 (unop j) := by
  haveI : Mono ((inclusion N i0 U0).app j) := by
    change Mono ((N.obj (op (unop j).1)).ofRestrict
      (stageOpen N i0 U0 (unop j)).isOpenEmbedding)
    infer_instance
  have hprojection : m.π.app (op (unop i).1) ≫ (tailDiagram N i0).map f =
      m.π.app (op (unop j).1) := by
    have hw := m.w ((tailInclusion i0).op.map f)
    change m.π.app (op (unop i).1) ≫ (tailDiagram N i0).map f =
      m.π.app (op (unop j).1) at hw
    exact hw
  apply (cancel_mono ((inclusion N i0 U0).app j)).1
  change (coneComponent N i0 m U0 (unop i) ≫ stageMap N i0 U0 f) ≫
      (N.obj (op (unop j).1)).ofRestrict (stageOpen N i0 U0 (unop j)).isOpenEmbedding =
    coneComponent N i0 m U0 (unop j) ≫
      (N.obj (op (unop j).1)).ofRestrict (stageOpen N i0 U0 (unop j)).isOpenEmbedding
  rw [Category.assoc, stageMap_fac, ← Category.assoc]
  change (coneComponent N i0 m U0 (unop i) ≫ (inclusion N i0 U0).app i) ≫
      (tailDiagram N i0).map f =
    coneComponent N i0 m U0 (unop j) ≫ (inclusion N i0 U0).app j
  rw [coneComponent_fac, Category.assoc, hprojection, ← coneComponent_fac]

/-- The actual cone of restrictions, literally based at the original cone
point restricted to the inverse image of `U0`. -/
@[expose] def restrictedCone (m : Cone N) (U0 : Opens (N.obj (op i0))) :
    Cone (restricted N i0 U0) where
  pt := m.pt.restrict (coneOpen N i0 m U0).isOpenEmbedding
  π := {
    app := fun i => coneComponent N i0 m U0 (unop i)
    naturality := by
      intro i j f
      simpa only [Functor.const_obj_map, Functor.const_obj_obj, restricted,
        Category.id_comp] using
          (coneComponent_naturality N i0 m U0 f).symm
  }

omit [IsDirectedOrder ι] in
/-- The principal-stage inverse-image open is the original named open. -/
theorem stageOpen_base (U0 : Opens (N.obj (op i0))) :
    stageOpen N i0 U0 (⟨i0, le_refl i0⟩ : Set.Ici i0) = U0 := by
  have heq : transition N i0 (⟨i0, le_refl i0⟩ : Set.Ici i0) =
      𝟙 (N.obj (op i0)) := by
    unfold transition
    convert N.map_id (op i0) using 1
  rw [stageOpen, heq, id_hom_base, Opens.map_id_obj]

/-- Cofinality transfers an original native limit to the opposite tail. -/
def tailIsLimit (m : Cone N) (hm : IsLimit m) :
    IsLimit (m.whisker (tailInclusion i0).op) :=
  (Functor.Initial.isLimitWhiskerEquiv (tailInclusion i0).op m).symm hm

/-- The original-limit lift of a cone on the restricted native diagram. -/
def originalLift (m : Cone N) (hm : IsLimit m)
    (U0 : Opens (N.obj (op i0))) (t : Cone (restricted N i0 U0)) : t.pt ⟶ m.pt :=
  (tailIsLimit N i0 m hm).lift ((Cone.postcompose (inclusion N i0 U0)).obj t)

/-- The lift obeys the original native projection equation at each stage. -/
theorem originalLift_fac (m : Cone N) (hm : IsLimit m)
    (U0 : Opens (N.obj (op i0))) (t : Cone (restricted N i0 U0))
    (i : Set.Ici i0) :
    originalLift N i0 m hm U0 t ≫ m.π.app (op i.1) =
      t.π.app (op i) ≫ (inclusion N i0 U0).app (op i) := by
  exact (tailIsLimit N i0 m hm).fac ((Cone.postcompose (inclusion N i0 U0)).obj t)
    (op i)

/-- The original-limit lift lands in the inverse image of the distinguished
open, including when any of the carrier spaces or opens is empty. -/
theorem originalLift_range (m : Cone N) (hm : IsLimit m)
    (U0 : Opens (N.obj (op i0))) (t : Cone (restricted N i0 U0)) :
    Set.range (originalLift N i0 m hm U0 t).hom.base ⊆
      Set.range (m.pt.ofRestrict (coneOpen N i0 m U0).isOpenEmbedding).hom.base := by
  let base : Set.Ici i0 := ⟨i0, le_refl i0⟩
  rintro _ ⟨x, rfl⟩
  have hmem : ((inclusion N i0 U0).app (op base)).hom.base
      ((t.π.app (op base)).hom.base x) ∈ U0 := by
    have hstage : ((inclusion N i0 U0).app (op base)).hom.base
        ((t.π.app (op base)).hom.base x) ∈ stageOpen N i0 U0 base := by
      change ((t.π.app (op base)).hom.base x).1 ∈ _
      exact ((t.π.app (op base)).hom.base x).2
    rw [stageOpen_base N i0 U0] at hstage
    exact hstage
  have heq : (m.π.app (op i0)).hom.base
      ((originalLift N i0 m hm U0 t).hom.base x) =
      ((inclusion N i0 U0).app (op base)).hom.base
        ((t.π.app (op base)).hom.base x) := by
    have hfac := originalLift_fac N i0 m hm U0 t base
    exact congrArg (fun f : t.pt ⟶ N.obj (op i0) => f.hom.base x) hfac
  refine ⟨⟨(originalLift N i0 m hm U0 t).hom.base x, ?_⟩, rfl⟩
  change (m.π.app (op i0)).hom.base
    ((originalLift N i0 m hm U0 t).hom.base x) ∈ U0
  exact heq ▸ hmem

/-- Factor the original lift through the canonical open immersion, retaining
the entire native sheafed-space morphism rather than just its base map. -/
def restrictedLift (m : Cone N) (hm : IsLimit m)
    (U0 : Opens (N.obj (op i0))) (t : Cone (restricted N i0 U0)) :
    t.pt ⟶ m.pt.restrict (coneOpen N i0 m U0).isOpenEmbedding := by
  let inclusion := (m.pt.ofRestrict (coneOpen N i0 m U0).isOpenEmbedding).hom
  let composite := (originalLift N i0 m hm U0 t).hom
  haveI : PresheafedSpace.IsOpenImmersion inclusion := by
    dsimp [inclusion]
    infer_instance
  exact InducedCategory.homMk (PresheafedSpace.IsOpenImmersion.lift
    inclusion composite (originalLift_range N i0 m hm U0 t))

/-- The factorization through the open immersion is a native equality. -/
theorem restrictedLift_fac (m : Cone N) (hm : IsLimit m)
    (U0 : Opens (N.obj (op i0))) (t : Cone (restricted N i0 U0)) :
    restrictedLift N i0 m hm U0 t ≫
      m.pt.ofRestrict (coneOpen N i0 m U0).isOpenEmbedding =
      originalLift N i0 m hm U0 t := by
  apply InducedCategory.hom_ext
  unfold restrictedLift
  dsimp
  exact PresheafedSpace.IsOpenImmersion.lift_fac _ _
    (originalLift_range N i0 m hm U0 t)

set_option maxHeartbeats 1200000 in
theorem restrictedLift_component (m : Cone N) (hm : IsLimit m)
    (U0 : Opens (N.obj (op i0))) (t : Cone (restricted N i0 U0))
    (i : Set.Ici i0) :
    restrictedLift N i0 m hm U0 t ≫ coneComponent N i0 m U0 i = t.π.app (op i) := by
  let inclusionArrow := m.pt.ofRestrict (coneOpen N i0 m U0).isOpenEmbedding
  let stageInclusion := (N.obj (op i.1)).ofRestrict
    (stageOpen N i0 U0 i).isOpenEmbedding
  haveI : Mono stageInclusion := by dsimp [stageInclusion]; infer_instance
  have hcomponent : coneComponent N i0 m U0 i ≫ stageInclusion =
      inclusionArrow ≫ m.π.app (op i.1) := coneComponent_fac N i0 m U0 i
  have hfactor : restrictedLift N i0 m hm U0 t ≫ inclusionArrow =
      originalLift N i0 m hm U0 t := restrictedLift_fac N i0 m hm U0 t
  have hprojection : originalLift N i0 m hm U0 t ≫ m.π.app (op i.1) =
      t.π.app (op i) ≫ stageInclusion := originalLift_fac N i0 m hm U0 t i
  apply (cancel_mono stageInclusion).1
  calc
    (restrictedLift N i0 m hm U0 t ≫ coneComponent N i0 m U0 i) ≫ stageInclusion =
        restrictedLift N i0 m hm U0 t ≫
          (coneComponent N i0 m U0 i ≫ stageInclusion) :=
            Category.assoc _ _ _
    _ = restrictedLift N i0 m hm U0 t ≫
          (inclusionArrow ≫ m.π.app (op i.1)) := congrArg _ hcomponent
    _ = (restrictedLift N i0 m hm U0 t ≫ inclusionArrow) ≫
          m.π.app (op i.1) := (Category.assoc _ _ _).symm
    _ = originalLift N i0 m hm U0 t ≫ m.π.app (op i.1) :=
          congrArg (· ≫ m.π.app (op i.1)) hfactor
    _ = t.π.app (op i) ≫ stageInclusion := hprojection

/-- Restriction of an arbitrary native limit cone to the principal tail and
the inverse-image opens is again a genuine native limit cone. -/
def restrictedIsLimit (m : Cone N) (hm : IsLimit m)
    (U0 : Opens (N.obj (op i0))) : IsLimit (restrictedCone N i0 m U0) where
  lift t := restrictedLift N i0 m hm U0 t
  fac t i := restrictedLift_component N i0 m hm U0 t (unop i)
  uniq t arrow h := by
    let inclusionArrow := m.pt.ofRestrict (coneOpen N i0 m U0).isOpenEmbedding
    have heq : arrow ≫ inclusionArrow = originalLift N i0 m hm U0 t := by
      apply (tailIsLimit N i0 m hm).hom_ext
      intro i
      have hfac : arrow ≫ coneComponent N i0 m U0 (unop i) = t.π.app i := by
        exact h i
      change (arrow ≫ inclusionArrow) ≫ m.π.app (op (unop i).1) =
        originalLift N i0 m hm U0 t ≫ m.π.app (op (unop i).1)
      calc
        _ = arrow ≫ (inclusionArrow ≫ m.π.app (op (unop i).1)) :=
              Category.assoc _ _ _
        _ = arrow ≫ (coneComponent N i0 m U0 (unop i) ≫
              (inclusion N i0 U0).app i) :=
                congrArg _ (coneComponent_fac N i0 m U0 (unop i)).symm
        _ = (arrow ≫ coneComponent N i0 m U0 (unop i)) ≫
              (inclusion N i0 U0).app i := (Category.assoc _ _ _).symm
        _ = t.π.app i ≫ (inclusion N i0 U0).app i :=
              congrArg (· ≫ (inclusion N i0 U0).app i) hfac
        _ = _ := (originalLift_fac N i0 m hm U0 t (unop i)).symm
    apply (cancel_mono inclusionArrow).1
    exact heq.trans (restrictedLift_fac N i0 m hm U0 t).symm

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
