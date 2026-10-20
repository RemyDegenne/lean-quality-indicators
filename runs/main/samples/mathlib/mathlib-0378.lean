@[expose] public section

universe u v

open CategoryTheory

attribute [instance] BddOrd.isBoundedOrder

namespace BddOrd

@[ext]
lemma ext {X Y : BddOrd} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

end BddOrd
end
