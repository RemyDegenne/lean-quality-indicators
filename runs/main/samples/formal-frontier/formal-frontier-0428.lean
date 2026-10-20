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

theorem sheafMate_comp {X Y Z : SheafedSpace A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sheafMate A (f ≫ g) =
      TopCat.Sheaf.pullbackCompInv A f.hom.base g.hom.base Z.sheaf ≫
        (TopCat.Sheaf.pullback A f.hom.base).map (sheafMate A g) ≫
        sheafMate A f := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction A
    (f ≫ g).hom.base).homEquiv _ _).injective
  rw [sheafMate_adjoint]
  have hmate := mateComp A f.hom.base g.hom.base (sheafMate A g) (sheafMate A f)
  rw [sheafMate_adjoint, sheafMate_adjoint] at hmate
  convert hmate.symm using 1; rfl

end AlgebraicGeometry.SheafedSpace
end
end
