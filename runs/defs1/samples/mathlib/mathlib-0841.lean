@[expose] public section

universe w v u

namespace CategoryTheory.Functor

open Opposite

variable {C : Type u} [Category.{v} C]

variable {F : Cᵒᵖ ⥤ Type w} {X : C} {x : F.obj (op X)}

/-- The canonical representation induced by the universal element `x : F.obj X`. -/
noncomputable def IsRepresentedBy.representableBy (h : F.IsRepresentedBy x) :
    F.RepresentableBy X :=
  Functor.representableByUliftFunctorEquiv.{v}
    ((RepresentableBy.equivUliftYonedaIso _ _).symm h.uliftYonedaIso)

end CategoryTheory.Functor
end
