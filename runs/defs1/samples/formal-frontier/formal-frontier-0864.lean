public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace TopCat.Sheaf.SquareTransition

variable (A : Type u) [Category.{w} A]

variable {FA : A → A → Type*} {CA : A → Type w}

variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]

variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]

variable [PreservesLimits (CategoryTheory.forget A)]

variable [PreservesFilteredColimits (CategoryTheory.forget A)]

variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

variable {Xj Xi Yj Yi : TopCat.{w}}

/-- The pullback comparison across the square as a natural isomorphism. -/
def pullbackSquareIso (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q) :
    pullback A q ⋙ pullback A fj ≅
      pullback A fi ⋙ pullback A p :=
  pullbackCompIso A fj q ≪≫ pullbackEqIso A h ≪≫
    (pullbackCompIso A p fi).symm

end TopCat.Sheaf.SquareTransition
end
end
