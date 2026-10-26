/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module
public import SheafCohomology.NativeAdditiveGlobalSections
public import SheafCohomology.NativeSpectralCylinder

public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Additive sections of native compact-open cylinders

Sections over the original cone point's compact-open cylinder arise as the
filtered colimit of the actual native restrictions of the original stages.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (S : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v})
    (i0 : ι) (m : Cone S) (U0 : Opens (S.obj (op i0)))

/-- Comparison from sections of the actual restricted stages to sections of
the original cone point over its named inverse-image open. -/
@[expose] noncomputable def nativeAdditiveCylinderSectionsComparison :
    colimit ((restricted S i0 U0).rightOp ⋙ SheafedSpace.Γ) ⟶
      m.pt.presheaf.obj (op (coneOpen S i0 m U0)) :=
  SheafedSpace.nativeAdditiveGlobalSectionsComparison
    (restricted S i0 U0) (restrictedCone S i0 m U0) ≫
    eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m U0))

omit [IsDirectedOrder ι] in
/-- The restricted-stage coprojection is the actual restricted-cone projection. -/
theorem colimit_ι_nativeAdditiveCylinderSectionsComparison (i : Set.Ici i0) :
    colimit.ι ((restricted S i0 U0).rightOp ⋙ SheafedSpace.Γ) i ≫
        nativeAdditiveCylinderSectionsComparison S i0 m U0 =
      SheafedSpace.Γ.map ((restrictedCone S i0 m U0).π.app (op i)).op ≫
        eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m U0)) := by
  unfold nativeAdditiveCylinderSectionsComparison
  rw [← Category.assoc,
    SheafedSpace.colimit_ι_nativeAdditiveGlobalSectionsComparison]

omit [IsDirectedOrder ι] in
/-- The original-stage arrow law, including both named-open transports. -/
theorem originalStage_nativeAdditiveCylinderSectionsComparison (i : Set.Ici i0) :
    eqToHom (SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 U0 i)).symm ≫
      colimit.ι ((restricted S i0 U0).rightOp ⋙ SheafedSpace.Γ) i ≫
        nativeAdditiveCylinderSectionsComparison S i0 m U0 =
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
            nativeAdditiveCylinderSectionsComparison S i0 m U0) :=
        Category.assoc _ _ _
    _ = eqToHom (SheafedSpace.restrict_Γ_obj (S.obj (op i.1))
          (stageOpen S i0 U0 i)).symm ≫
          (SheafedSpace.Γ.map ((restrictedCone S i0 m U0).π.app (op i)).op ≫
            eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m U0))) :=
        congrArg (eqToHom (SheafedSpace.restrict_Γ_obj (S.obj (op i.1))
          (stageOpen S i0 U0 i)).symm ≫ ·)
          (colimit_ι_nativeAdditiveCylinderSectionsComparison S i0 m U0 i)
    _ = _ := by
      simp only [restrictedCone]
      rw [hcomponent]
      exact SheafedSpace.restrictOnNamedPreimage_Γ_map
        (m.π.app (op i.1)) (stageOpen S i0 U0 i)
        (coneOpen S i0 m U0) (coneOpen_eq_stage S i0 m U0 i)

/-- For an original limiting cone, compact-open additive cylinder sections
are exactly the filtered colimit of sections of its actual restricted stages. -/
theorem isIso_nativeAdditiveCylinderSectionsComparison (hm : IsLimit m)
    (hstage : ∀ k : ιᵒᵖ,
      SpectralSpace ((S ⋙ SheafedSpace.forget AddCommGrpCat.{v}).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((S ⋙ SheafedSpace.forget AddCommGrpCat.{v}).map f))
    (hU0 : IsCompact (U0 : Set (S.obj (op i0)))) :
    IsIso (nativeAdditiveCylinderSectionsComparison S i0 m U0) := by
  letI : Nonempty (Set.Ici i0) := ⟨⟨i0, le_refl i0⟩⟩
  letI : IsDirectedOrder (Set.Ici i0) := tailDirectedOrder i0
  letI : IsFiltered (Set.Ici i0) := inferInstance
  let R := restricted S i0 U0
  let mR := restrictedCone S i0 m U0
  have hmR : IsLimit mR := restrictedIsLimit S i0 m hm U0
  have hRstage : ∀ k : (Set.Ici i0)ᵒᵖ,
      SpectralSpace ((R ⋙ SheafedSpace.forget AddCommGrpCat.{v}).obj k) :=
    spectralStage S i0 U0 hstage htransition hU0
  have hRtransition : ∀ {k l : (Set.Ici i0)ᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((R ⋙ SheafedSpace.forget AddCommGrpCat.{v}).map f) :=
    fun {_ _} f => spectralStageMap S i0 U0 hstage htransition hU0 f
  have hnative : IsIso (SheafedSpace.nativeAdditiveGlobalSectionsComparison R mR) :=
    SheafedSpace.isIso_nativeAdditiveGlobalSectionsComparison
      R mR hmR hRstage hRtransition
  exact IsIso.comp_isIso' hnative inferInstance

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
