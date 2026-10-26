/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module
public import SheafCohomology.NativeStageSectionColimit
public import SheafCohomology.LimitConstruction
public import SpectralStoneDuality.Limits
public import Mathlib.Topology.QuasiSeparated

public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Global sections of a chosen native limit

The colimit of the native global sections of a filtered spectral diagram maps
isomorphically to the global sections of the limit constructed from an actual
underlying-space limiting cone. The comparison uses the genuine native
projections, not alternate sheaf or space models.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace

variable {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : Jᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} (Type v))
    (c : Cone (N ⋙ SheafedSpace.forget (Type v))) (hc : IsLimit c)

/-- The cocone of global-section maps of the actual native limit projections. -/
@[expose] noncomputable def nativeGlobalSectionsCocone :
    Cocone (N.rightOp ⋙ SheafedSpace.Γ) where
  pt := SheafedSpace.Γ.obj (op (limitConeOfSpaceCone (Type v) N c hc).cone.pt)
  ι := {
    app i := SheafedSpace.Γ.map
      ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i)).op
    naturality := by
      intro i j f
      change SheafedSpace.Γ.map (N.map f.op).op ≫
          SheafedSpace.Γ.map
            ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op j)).op =
        SheafedSpace.Γ.map
          ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i)).op ≫ 𝟙 _
      rw [Category.comp_id]
      rw [← SheafedSpace.Γ.map_comp]
      congr 1
      rw [← op_comp, (limitConeOfSpaceCone (Type v) N c hc).cone.w f.op]
  }

/-- The actual global-section comparison determined by the native projections. -/
@[expose] noncomputable def nativeGlobalSectionsComparison :
    colimit (N.rightOp ⋙ SheafedSpace.Γ) ⟶
      SheafedSpace.Γ.obj (op (limitConeOfSpaceCone (Type v) N c hc).cone.pt) :=
  colimit.desc _ (nativeGlobalSectionsCocone N c hc)

omit [IsFiltered J] in
/-- The comparison's stage leg is the native projection's global-section map. -/
theorem colimit_ι_nativeGlobalSectionsComparison (i : J) :
    colimit.ι (N.rightOp ⋙ SheafedSpace.Γ) i ≫
        nativeGlobalSectionsComparison N c hc =
      SheafedSpace.Γ.map
        ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i)).op := by
  simpa only [nativeGlobalSectionsComparison, nativeGlobalSectionsCocone] using
    (colimit.ι_desc (nativeGlobalSectionsCocone N c hc) i)

omit [IsFiltered J] in
/-- The same native comparison factors through moving-stage sections and the
fixed-base compact-open evaluation comparison. -/
theorem nativeGlobalSectionsComparison_eq_colimMap_post :
    letI : HasColimitsOfShape J (c.pt.Sheaf (Type v)) :=
      CategoryTheory.Sheaf.instHasColimitsOfShape
    nativeGlobalSectionsComparison N c hc =
      colimMap (SheafCohomology.ConePullbackSections.coneSections N c) ≫
        colimit.post (conePullback (Type v) N c)
          (SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)) := by
  letI : HasColimitsOfShape J (c.pt.Sheaf (Type v)) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
  let S : J ⥤ Type v := N.rightOp ⋙ SheafedSpace.Γ
  let R : J ⥤ c.pt.Sheaf (Type v) := conePullback (Type v) N c
  let E : c.pt.Sheaf (Type v) ⥤ Type v :=
    SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)
  let η : S ⟶ R ⋙ E := SheafCohomology.ConePullbackSections.coneSections N c
  apply colimit.hom_ext
  intro i
  have hprojection : η.app i ≫ E.map (colimit.ι R i) =
      SheafedSpace.Γ.map
        ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i)).op := by
    change (SheafCohomology.ConePullbackSections.coneSections N c).app i ≫
        (colimit.ι (conePullback (Type v) N c) i).hom.app (op (⊤ : Opens c.pt)) =
      ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i)).hom.c.app (op ⊤)
    rw [← limitConeOfSpaceCone_π_mate_colimit_ι (Type v) N c hc i,
      SheafCohomology.ConePullbackSections.coneSections_app]
    have hfactor := SheafCohomology.ConePullbackSections.adjointSectionMap_eq_unit_comp
      ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i)).hom.base
      (sheafMate (Type v) ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i))) ⊤
    have hunit := congrArg
      (fun e ↦ e.hom.app (op (⊤ : Opens (N.obj (op i) : TopCat))))
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i)).hom.base).homEquiv_unit
          (f := sheafMate (Type v)
            ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i))))
    have hmate := congrArg
      (fun e ↦ e.hom.app (op (⊤ : Opens (N.obj (op i) : TopCat))))
      (sheafMate_adjoint (Type v)
        ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i)))
    calc
      _ = SheafCohomology.ConePullbackSections.adjointSectionMap
          ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i)).hom.base
          (sheafMate (Type v)
            ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i))) ⊤ := by
        convert hfactor.symm using 1
        all_goals rfl
      _ = ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
          ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i)).hom.base).homEquiv _ _
            (sheafMate (Type v)
              ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i)))).hom.app
                (op (⊤ : Opens (N.obj (op i) : TopCat))) := hfactor.trans hunit.symm
      _ = _ := hmate
  change colimit.ι S i ≫ nativeGlobalSectionsComparison N c hc =
    colimit.ι S i ≫ (colimMap η ≫ colimit.post R E)
  calc
    colimit.ι S i ≫ nativeGlobalSectionsComparison N c hc =
        SheafedSpace.Γ.map
          ((limitConeOfSpaceCone (Type v) N c hc).cone.π.app (op i)).op :=
      colimit_ι_nativeGlobalSectionsComparison N c hc i
    _ = η.app i ≫ E.map (colimit.ι R i) := hprojection.symm
    _ = colimit.ι S i ≫ (colimMap η ≫ colimit.post R E) := by
      rw [← Category.assoc,
        SheafCohomology.ConePullbackSections.colimit_ι_colimMap_coneSections,
        Category.assoc, colimit.ι_post]

omit [IsFiltered J] in
include hc in
private theorem compactSpace_conePoint
    (hstage : ∀ k : Jᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f)) :
    CompactSpace c.pt := by
  let e := TopCat.homeoOfIso (hc.conePointUniqueUpToIso
    (TopCat.limitConeIsLimit (N ⋙ SheafedSpace.forget (Type v))))
  letI := SpectralStoneDuality.compactSpace_limit_of_spectral
    (N ⋙ SheafedSpace.forget (Type v)) hstage htransition
  exact e.symm.compactSpace

include hc in
private theorem prespectralSpace_conePoint
    (hstage : ∀ k : Jᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f)) :
    PrespectralSpace c.pt := by
  let e := TopCat.homeoOfIso (hc.conePointUniqueUpToIso
    (TopCat.limitConeIsLimit (N ⋙ SheafedSpace.forget (Type v))))
  letI := SpectralStoneDuality.prespectralSpace_limit_of_spectral
    (N ⋙ SheafedSpace.forget (Type v)) hstage htransition
  exact e.isOpenEmbedding.prespectralSpace

include hc in
private theorem quasiSeparatedSpace_conePoint
    (hstage : ∀ k : Jᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f)) :
    QuasiSeparatedSpace c.pt := by
  let e := TopCat.homeoOfIso (hc.conePointUniqueUpToIso
    (TopCat.limitConeIsLimit (N ⋙ SheafedSpace.forget (Type v))))
  letI := SpectralStoneDuality.quasiSeparatedSpace_limit_of_spectral
    (N ⋙ SheafedSpace.forget (Type v)) hstage htransition
  exact e.isOpenEmbedding.quasiSeparatedSpace

/-- Global sections of the chosen native limit of a filtered spectral diagram
are the colimit of its actual native stage global sections. -/
theorem isIso_nativeGlobalSectionsComparison
    (hstage : ∀ k : Jᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f)) :
    IsIso (nativeGlobalSectionsComparison N c hc) := by
  letI : HasColimitsOfShape J (c.pt.Sheaf (Type v)) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
  letI : CompactSpace c.pt := compactSpace_conePoint N c hc hstage htransition
  letI : PrespectralSpace c.pt := prespectralSpace_conePoint N c hc hstage htransition
  letI : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_conePoint N c hc hstage htransition
  rw [nativeGlobalSectionsComparison_eq_colimMap_post]
  exact IsIso.comp_isIso' (isIso_colimMap_coneSections N c hc hstage htransition)
    (SheafCohomology.CompactOpenSections.canonicalSectionsComparison_isIso
      (conePullback (Type v) N c) (⊤ : Opens c.pt)
      (by simpa only [Opens.coe_top] using (isCompact_univ : IsCompact (Set.univ : Set c.pt))))

end AlgebraicGeometry.SheafedSpace
