public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C]

/-- A morphism factors through an object satisfying `P` if it has a factorisation whose midpoint
satisfies `P`. -/
def FactorsThrough (P : ObjectProperty C) {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ d : Factorisation f, P d.mid

end CategoryTheory.ObjectProperty
end
