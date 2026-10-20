public section

set_option warningAsError true

set_option linter.style.haveILetI false

set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace

variable {J : Type v} [SmallCategory J]
    (S : Jᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} CommRingCat.{v}) (m : Cone S)

/-- The cocone of ring sections induced by the original native projections. -/
@[expose] noncomputable def nativeCommRingGlobalSectionsCocone :
    Cocone (S.rightOp ⋙ SheafedSpace.Γ) where
  pt := SheafedSpace.Γ.obj (op m.pt)
  ι := {
    app i := SheafedSpace.Γ.map (m.π.app (op i)).op
    naturality := by
      intro i j f
      change SheafedSpace.Γ.map (S.map f.op).op ≫
          SheafedSpace.Γ.map (m.π.app (op j)).op =
        SheafedSpace.Γ.map (m.π.app (op i)).op ≫ 𝟙 _
      rw [Category.comp_id]
      rw [← SheafedSpace.Γ.map_comp]
      congr 1
      rw [← op_comp, m.w f.op]
  }

end AlgebraicGeometry.SheafedSpace
end
end
