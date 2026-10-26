/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Builds on the native additive cylinder and the generic spectral cylinder.
-/




module
public import SheafCohomology.NativeCommRingGlobalSections
public import SheafCohomology.NativeSpectralCylinder

public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Ring sections over native compact-open cylinders

The comparison from sections of the actual restricted tail stages targets
sections on the original cone's named open. Both source and target transports
are explicit in the original-projection law.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (S : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} CommRingCat.{v})
    (i0 : ι) (m : Cone S) (U0 : Opens (S.obj (op i0)))

/-- Comparison from the actual restricted-stage rings to the original cone's
sections on its named inverse-image open. -/
@[expose] noncomputable def nativeCommRingCylinderSectionsComparison :
    colimit ((restricted S i0 U0).rightOp ⋙ SheafedSpace.Γ) ⟶
      m.pt.presheaf.obj (op (coneOpen S i0 m U0)) :=
  SheafedSpace.nativeCommRingGlobalSectionsComparison
    (restricted S i0 U0) (restrictedCone S i0 m U0) ≫
    eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m U0))

omit [IsDirectedOrder ι] in
/-- The coprojection maps through the actual restricted-cone projection. -/
theorem colimit_ι_nativeCommRingCylinderSectionsComparison (i : Set.Ici i0) :
    colimit.ι ((restricted S i0 U0).rightOp ⋙ SheafedSpace.Γ) i ≫
        nativeCommRingCylinderSectionsComparison S i0 m U0 =
      SheafedSpace.Γ.map ((restrictedCone S i0 m U0).π.app (op i)).op ≫
        eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m U0)) := by
  unfold nativeCommRingCylinderSectionsComparison
  rw [← Category.assoc,
    SheafedSpace.colimit_ι_nativeCommRingGlobalSectionsComparison]

omit [IsDirectedOrder ι] in
/-- The original projection's ring map, with inverse stage transport and
forward cone transport, agrees with the restricted-stage coprojection. -/
theorem originalStage_nativeCommRingCylinderSectionsComparison (i : Set.Ici i0) :
    eqToHom (SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 U0 i)).symm ≫
      colimit.ι ((restricted S i0 U0).rightOp ⋙ SheafedSpace.Γ) i ≫
        nativeCommRingCylinderSectionsComparison S i0 m U0 =
      (m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 U0 i)) ≫
        eqToHom (congrArg
          (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
          (coneOpen_eq_stage S i0 m U0 i).symm) := by
  have hcomponent : coneComponent S i0 m U0 i =
      SheafedSpace.restrictOnNamedPreimage (m.π.app (op i.1))
        (stageOpen S i0 U0 i) (coneOpen S i0 m U0)
        (coneOpen_eq_stage S i0 m U0 i) := by
    haveI : Mono ((S.obj (op i.1)).ofRestrict
        (stageOpen S i0 U0 i).isOpenEmbedding) := inferInstance
    apply (cancel_mono ((S.obj (op i.1)).ofRestrict
      (stageOpen S i0 U0 i).isOpenEmbedding)).1
    exact (coneComponent_fac S i0 m U0 i).trans
      (SheafedSpace.restrictOnNamedPreimage_fac
        (m.π.app (op i.1)) (stageOpen S i0 U0 i)
        (coneOpen S i0 m U0) (coneOpen_eq_stage S i0 m U0 i)).symm
  calc
    _ = eqToHom (SheafedSpace.restrict_Γ_obj (S.obj (op i.1))
          (stageOpen S i0 U0 i)).symm ≫
          (colimit.ι ((restricted S i0 U0).rightOp ⋙ SheafedSpace.Γ) i ≫
            nativeCommRingCylinderSectionsComparison S i0 m U0) :=
        Category.assoc _ _ _
    _ = eqToHom (SheafedSpace.restrict_Γ_obj (S.obj (op i.1))
          (stageOpen S i0 U0 i)).symm ≫
          (SheafedSpace.Γ.map ((restrictedCone S i0 m U0).π.app (op i)).op ≫
            eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m U0))) :=
        congrArg (eqToHom (SheafedSpace.restrict_Γ_obj (S.obj (op i.1))
          (stageOpen S i0 U0 i)).symm ≫ ·)
          (colimit_ι_nativeCommRingCylinderSectionsComparison S i0 m U0 i)
    _ = _ := by
      simp only [restrictedCone]
      rw [hcomponent]
      exact SheafedSpace.restrictOnNamedPreimage_Γ_map
        (m.π.app (op i.1)) (stageOpen S i0 U0 i)
        (coneOpen S i0 m U0) (coneOpen_eq_stage S i0 m U0 i)

/-- Spectral stages and transitions identify the original named-open section
ring with the filtered colimit of actual restricted-stage rings. -/
theorem isIso_nativeCommRingCylinderSectionsComparison (hm : IsLimit m)
    (hstage : ∀ k : ιᵒᵖ,
      SpectralSpace ((S ⋙ SheafedSpace.forget CommRingCat.{v}).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((S ⋙ SheafedSpace.forget CommRingCat.{v}).map f))
    (hU0 : IsCompact (U0 : Set (S.obj (op i0)))) :
    IsIso (nativeCommRingCylinderSectionsComparison S i0 m U0) := by
  letI : Nonempty (Set.Ici i0) := ⟨⟨i0, le_refl i0⟩⟩
  letI : IsDirectedOrder (Set.Ici i0) := tailDirectedOrder i0
  letI : IsFiltered (Set.Ici i0) := inferInstance
  let R := restricted S i0 U0
  let mR := restrictedCone S i0 m U0
  have hmR : IsLimit mR := restrictedIsLimit S i0 m hm U0
  have hRstage : ∀ k : (Set.Ici i0)ᵒᵖ,
      SpectralSpace ((R ⋙ SheafedSpace.forget CommRingCat.{v}).obj k) :=
    spectralStage S i0 U0 hstage htransition hU0
  have hRtransition : ∀ {k l : (Set.Ici i0)ᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((R ⋙ SheafedSpace.forget CommRingCat.{v}).map f) :=
    fun {_ _} f => spectralStageMap S i0 U0 hstage htransition hU0 f
  have hnative : IsIso (SheafedSpace.nativeCommRingGlobalSectionsComparison R mR) :=
    SheafedSpace.isIso_nativeCommRingGlobalSectionsComparison
      R mR hmR hRstage hRtransition
  exact IsIso.comp_isIso' hnative inferInstance

/-- Each original named-open section comes from some original tail-stage open,
via the actual original projection (not necessarily from a fixed stage). -/
theorem exists_nativeCommRingCylinderSections_stage (hm : IsLimit m)
    (hstage : ∀ k : ιᵒᵖ,
      SpectralSpace ((S ⋙ SheafedSpace.forget CommRingCat.{v}).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((S ⋙ SheafedSpace.forget CommRingCat.{v}).map f))
    (hU0 : IsCompact (U0 : Set (S.obj (op i0))))
    (r : m.pt.presheaf.obj (op (coneOpen S i0 m U0))) :
    ∃ (i : Set.Ici i0)
        (a : (S.obj (op i.1)).presheaf.obj (op (stageOpen S i0 U0 i))),
      ((m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 U0 i)) ≫
        eqToHom (congrArg
          (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
          (coneOpen_eq_stage S i0 m U0 i).symm)) a = r := by
  letI : Nonempty (Set.Ici i0) := ⟨⟨i0, le_refl i0⟩⟩
  letI : IsDirectedOrder (Set.Ici i0) := tailDirectedOrder i0
  letI : IsFiltered (Set.Ici i0) := inferInstance
  let R := restricted S i0 U0
  let mR := restrictedCone S i0 m U0
  have hmR : IsLimit mR := restrictedIsLimit S i0 m hm U0
  have hRstage : ∀ k : (Set.Ici i0)ᵒᵖ,
      SpectralSpace ((R ⋙ SheafedSpace.forget CommRingCat.{v}).obj k) :=
    spectralStage S i0 U0 hstage htransition hU0
  have hRtransition : ∀ {k l : (Set.Ici i0)ᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((R ⋙ SheafedSpace.forget CommRingCat.{v}).map f) :=
    fun {_ _} f => spectralStageMap S i0 U0 hstage htransition hU0 f
  let hcone := SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m U0)
  obtain ⟨i, aR, haR⟩ := SheafedSpace.exists_nativeCommRingGlobalSections_stage
    R mR hmR hRstage hRtransition ((eqToHom hcone.symm) r)
  let hstageCast := SheafedSpace.restrict_Γ_obj (S.obj (op i.1))
    (stageOpen S i0 U0 i)
  refine ⟨i, (eqToHom hstageCast) aR, ?_⟩
  have hleg := congrArg
    (fun arrow => arrow ((eqToHom hstageCast) aR))
    (originalStage_nativeCommRingCylinderSectionsComparison S i0 m U0 i)
  simp only [CommRingCat.comp_apply] at hleg
  simp only [CommRingCat.comp_apply]
  rw [← hleg]
  have hstageCancel : (eqToHom hstageCast.symm) ((eqToHom hstageCast) aR) = aR := by
    change (eqToHom hstageCast ≫ eqToHom hstageCast.symm) aR = aR
    simp
  rw [hstageCancel, ← CommRingCat.comp_apply]
  rw [colimit_ι_nativeCommRingCylinderSectionsComparison]
  simp only [CommRingCat.comp_apply]
  change (eqToHom hcone) (SheafedSpace.Γ.map (mR.π.app (op i)).op aR) = r
  rw [haR]
  change (eqToHom hcone.symm ≫ eqToHom hcone) r = r
  simp

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
