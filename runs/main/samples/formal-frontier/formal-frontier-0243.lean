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

variable {C : Type (v + 1)} [Category.{v} C]

variable (S : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C)
  (i0 j : ι) (h : i0 ≤ j) (U : Opens (S.obj (op i0)))

omit [IsDirectedOrder ι] in
theorem originalStage_cylinderSectionsTailIso (k : Set.Ici j) :
    eqToHom (SheafedSpace.restrict_Γ_obj (S.obj (op k.1))
        (stageOpen S j (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)) k)).symm ≫
      (cylinderSectionsTailIso S i0 j h U).hom.app k =
    eqToHom (congrArg
        (fun W : Opens (S.obj (op k.1)) => (S.obj (op k.1)).presheaf.obj (op W))
        (stageOpen_betweenTail S i0 j h U k)) ≫
      eqToHom (SheafedSpace.restrict_Γ_obj (S.obj (op k.1))
        (stageOpen S i0 U ((betweenTailInclusion i0 j h).obj k))).symm := by
  rw [cylinderSectionsTailIso_hom_app]
  simp only [eqToHom_trans]

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
end
end
