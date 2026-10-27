@[expose] public section

open Opposite

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

universe v u v' u'

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- The anti-equivalence between cosimplicial objects and simplicial objects. -/
@[simps!]
def cosimplicialSimplicialEquiv : (CosimplicialObject C)ᵒᵖ ≌ SimplicialObject Cᵒᵖ :=
  Functor.opUnopEquiv _ _

end CategoryTheory
end
