public section

set_option warningAsError true

set_option linter.style.haveILetI false

set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]

variable {C : Type (v + 1)} [Category.{v} C]

variable (N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C) (i0 : ι)

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

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
end
end
