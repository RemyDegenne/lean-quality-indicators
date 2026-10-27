public section

set_option warningAsError true

set_option linter.style.haveILetI false

set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency.types false

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

end AlgebraicGeometry.SheafedSpace
end
end
