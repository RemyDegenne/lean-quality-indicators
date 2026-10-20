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
    (S : Jᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v}) (m : Cone S)

/-- Comparison of additive stage sections with the actual cone vertex's sections. -/
@[expose] noncomputable def nativeAdditiveGlobalSectionsComparison :
    colimit (S.rightOp ⋙ SheafedSpace.Γ) ⟶ SheafedSpace.Γ.obj (op m.pt) :=
  colimit.desc _ (nativeAdditiveGlobalSectionsCocone S m)

end AlgebraicGeometry.SheafedSpace
end
end
