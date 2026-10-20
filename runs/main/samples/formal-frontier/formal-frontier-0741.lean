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

variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]

variable [PreservesLimits (CategoryTheory.forget A)]

variable [PreservesFilteredColimits (CategoryTheory.forget A)]

variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

variable {J : Type wj} [Category.{vj} J]

@[simp] theorem coneOfPullbackCocone_sheaf (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (K : Cocone (conePullback A S c)) :
    (coneOfPullbackCocone A S c K).pt.sheaf = K.pt := rfl

end AlgebraicGeometry.SheafedSpace
end
end
