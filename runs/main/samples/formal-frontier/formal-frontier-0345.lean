public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u vj wj

namespace AlgebraicGeometry.SheafedSpace

variable (A : Type u) [Category.{w} A]

variable {FA : A → A → Type*} {CA : A → Type w}

variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]

variable [instConcrete : ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]

variable [instPreservesLimits : PreservesLimits (CategoryTheory.forget A)]

variable [instPreservesFiltered : PreservesFilteredColimits (CategoryTheory.forget A)]

variable [instReflectsIsos : (CategoryTheory.forget A).ReflectsIsomorphisms]

variable {J : Type wj} [Category.{vj} J]

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforward_obj_sheaf (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y) (i : Jᵒᵖ) :
    ((diagramPushforward A N Y f).obj i).sheaf =
      (TopCat.Sheaf.pushforward A (f.app i)).obj (N.obj i).sheaf := rfl

end AlgebraicGeometry.SheafedSpace
end
end
