public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {X Y : C}

/-- An extremal epimorphism `f : X ⟶ Y` is an epimorphism which does not
factor through any proper subobject of `Y`. -/
class ExtremalEpi (f : X ⟶ Y) : Prop extends Epi f where
  isIso (f) {Z : C} (p : X ⟶ Z) (i : Z ⟶ Y) (fac : p ≫ i = f) [Mono i] : IsIso i

end CategoryTheory
end
