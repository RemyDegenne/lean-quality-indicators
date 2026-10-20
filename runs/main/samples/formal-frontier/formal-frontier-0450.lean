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

theorem adjoint_eq_homEquiv (p : Xj ⟶ Xi) {F : Xi.Sheaf A} {G : Xj.Sheaf A}
    (a : (pullback A p).obj F ⟶ G) :
    adjoint A p a = (pullbackPushforwardAdjunction A p).homEquiv F G a := by
  unfold adjoint
  rfl

end TopCat.Sheaf.SquareTransition
end
end
