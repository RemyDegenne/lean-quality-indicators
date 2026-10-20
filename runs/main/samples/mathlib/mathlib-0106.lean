@[expose] public section

universe w v₁ v u₁ u

namespace CategoryTheory

open Limits Opposite ConcreteCategory

variable {C : Type u} [Category.{v} C]

namespace Functor.Elements

theorem hasInitial_iff_isCorepresentable (F : C ⥤ Type w) :
    HasInitial (Elements F) ↔ IsCorepresentable F where
  mp _ := isCorepresentable_of_hasInitial F
  mpr _ := inferInstance

end Functor.Elements
end CategoryTheory
end
