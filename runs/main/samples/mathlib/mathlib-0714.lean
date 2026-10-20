@[expose] public section

universe v w u u'

open TypeCat CategoryTheory

namespace CategoryTheory

theorem types_comp {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ConcreteCategory.hom (f ≫ g) = g ∘ f :=
  rfl

end CategoryTheory
end
