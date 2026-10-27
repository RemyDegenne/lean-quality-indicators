@[expose] public section

namespace CategoryTheory

universe v u v₁ v₂ u₁ u₂

namespace Cat

variable (V : Type*) [ReflQuiver V]

variable {V} {W : Type*} [ReflQuiver W] (F : V ⥤rq W)

/-- We will make use of the natural quotient map from the free category on the underlying
quiver of a refl quiver to the free category on the reflexive quiver. -/
def freeReflNatTrans : ReflQuiv.forgetToQuiv ⋙ Cat.free ⟶ freeRefl where
  app V := (FreeRefl.quotientFunctor V).toCatHom
  naturality v w f := by
    ext1; exact Paths.ext_functor (V := Quiv.of v) (by cat_disch) (by cat_disch)

end Cat
end CategoryTheory
end
