@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Opposite

namespace Limits

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
  (F : Jᵒᵖ ⥤ J ⥤ C)

namespace Wedge

variable {F}

namespace IsLimit

variable {c : Wedge F} (hc : IsLimit c)

/-- Construct a morphism to the end from its universal property. -/
def lift (hc : IsLimit c) {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j) :
    X ⟶ c.pt :=
  Multifork.IsLimit.lift hc f (fun _ ↦ hf _)

end IsLimit
end Wedge
end Limits
end CategoryTheory
end
