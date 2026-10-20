@[expose] public section

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C]

namespace FilteredObject

variable {I : Type*} [Category I]

variable (C I) in
/-- The morphism property of strict morphisms of filtered objects. -/
abbrev isStrictHom : MorphismProperty (FilteredObject C I) :=
  fun _ _ f ↦ IsStrictHom f

end FilteredObject
end CategoryTheory
end
