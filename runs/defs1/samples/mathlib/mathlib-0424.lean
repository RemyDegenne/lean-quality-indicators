public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- A category is called balanced if any morphism that is both monic and epic is an isomorphism. -/
class Balanced : Prop where
  isIso_of_mono_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f], IsIso f

end CategoryTheory
end
