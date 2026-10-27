@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite Cardinal

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

attribute [local instance] fact_isRegular_aleph0

variable (C) in
/-- A morphism `f : X ⟶ Y` is finitely presentable if it is so as an object of `Under X`. -/
def MorphismProperty.isFinitelyPresentable : MorphismProperty C :=
  fun _ _ f ↦ ObjectProperty.isFinitelyPresentable.{w} _ (CategoryTheory.Under.mk f)

end CategoryTheory
end
