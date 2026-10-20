public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace TopCat.Sheaf

variable (A : Type u) [Category.{w} A]

variable {FA : A → A → Type*} {CA : A → Type w}

variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]

variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]

variable [PreservesLimits (CategoryTheory.forget A)]

variable [PreservesFilteredColimits (CategoryTheory.forget A)]

variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

variable {X Y Z : TopCat.{w}}

/-- The inverse composite-pullback comparison on one sheaf. -/
noncomputable abbrev pullbackCompInv (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Z.Sheaf A) :
    (pullback A (f ≫ g)).obj F ⟶
      (pullback A f).obj ((pullback A g).obj F) :=
  (pullbackCompIso A f g).inv.app F

end TopCat.Sheaf
end
end
