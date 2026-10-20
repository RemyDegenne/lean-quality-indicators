public section

set_option warningAsError true

set_option linter.style.haveILetI false

set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace

variable {C : Type (v + 1)} [Category.{v} C]

variable {X Y Z : SheafedSpace.{v + 1, v, v} C}

theorem restrict_Γ_obj (X : SheafedSpace.{v + 1, v, v} C) (U : Opens X) :
    Γ.obj (op (X.restrict U.isOpenEmbedding)) = X.presheaf.obj (op U) := by
  change X.presheaf.obj (op (U.isOpenEmbedding.functor.obj ⊤)) = _
  rw [Opens.isOpenEmbedding_obj_top]

end AlgebraicGeometry.SheafedSpace
end
end
