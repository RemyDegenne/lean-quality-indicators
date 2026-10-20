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

theorem pullbackCompIso_assoc
    {W : TopCat.{w}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Functor.isoWhiskerLeft (pullback A h) (pullbackCompIso A f g) ≪≫
        pullbackCompIso A (f ≫ g) h =
      (Functor.associator (pullback A h) (pullback A g)
          (pullback A f)).symm ≪≫
        Functor.isoWhiskerRight (pullbackCompIso A g h)
          (pullback A f) ≪≫
        pullbackCompIso A f (g ≫ h) :=
  Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _
    (pushforwardCompIso_assoc A f g h)

end TopCat.Sheaf
end
end
