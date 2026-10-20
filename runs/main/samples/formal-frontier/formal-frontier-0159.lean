public section

set_option warningAsError true

set_option linter.style.haveILetI false

set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (S : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} CommRingCat.{v})
    (i0 : ι) (m : Cone S) (U0 : Opens (S.obj (op i0)))

omit [IsDirectedOrder ι] in
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

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
end
end
