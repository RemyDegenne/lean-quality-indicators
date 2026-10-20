public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopCat.Sheaf.AbelianForget

universe v vj wj

namespace AlgebraicGeometry.SheafedSpace.AbelianForget

variable {J : Type wj} [Category.{vj} J]

theorem underlyingDiagram_forget (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v}) :
    (S ⋙ underlying) ⋙ SheafedSpace.forget (Type v) =
      S ⋙ SheafedSpace.forget AddCommGrpCat.{v} := by
  rfl

end AlgebraicGeometry.SheafedSpace.AbelianForget
end
end
