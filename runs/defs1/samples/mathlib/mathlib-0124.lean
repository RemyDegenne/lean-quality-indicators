@[expose] public section

open SetRel

namespace CategoryTheory

universe u

namespace RelCat

variable {X Y Z : RelCat.{u}}

section Opposite

open Opposite

set_option backward.isDefEq.respectTransparency.types false in
/-- The other direction of `opFunctor`. -/
def unopFunctor : RelCatᵒᵖ ⥤ RelCat where
  obj X := unop X
  map {_ _} r := .ofRel r.unop.rel.inv

end Opposite
end RelCat
end CategoryTheory
end
