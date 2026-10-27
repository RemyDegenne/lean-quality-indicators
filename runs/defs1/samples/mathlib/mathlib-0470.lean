@[expose] public section

noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open scoped AlgebraicGeometry

variable {C : Type u} [Category.{v} C]

variable {X Y : TopCat.{w}} (f : X ⟶ Y)

variable ⦃ι : Type w⦄ {U : ι → Opens Y}

namespace TopCat

namespace Sheaf

variable (C)

variable {C}

variable (A : Type*) [Category.{w} A] {FA : A → A → Type*} {CA : A → Type w}

variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA] [HasColimits A]

variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]

variable [PreservesFilteredColimits (CategoryTheory.forget A)]

variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/--
The pullback functor.
-/
def pullback (f : X ⟶ Y) : Y.Sheaf A ⥤ X.Sheaf A :=
  (Opens.map f).sheafPullback _ _ _

end Sheaf
end TopCat
end
end
