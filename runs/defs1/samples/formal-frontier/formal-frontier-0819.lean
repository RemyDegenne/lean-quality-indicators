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

/-- Transport a stage transition across a commuting triangle of spaces. -/
@[expose] def triangleMap {W X Y : TopCat.{w}} {p : W ⟶ X} {q : W ⟶ Y} {f : Y ⟶ X}
    {F : X.Sheaf A} {G : Y.Sheaf A} (triangle : q ≫ f = p)
    (a : (TopCat.Sheaf.pullback A f).obj F ⟶ G) :
    (TopCat.Sheaf.pullback A p).obj F ⟶
      (TopCat.Sheaf.pullback A q).obj G := by
  rw [← triangle]
  exact TopCat.Sheaf.pullbackCompInv A q f F ≫
    (TopCat.Sheaf.pullback A q).map a

end AlgebraicGeometry.SheafedSpace
end
end
