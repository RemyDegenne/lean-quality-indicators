@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

section Fibrant

variable [CategoryWithFibrations C] [HasTerminal C]

variable (C) in
/-- The property that is satisfied by fibrant objects.
(This is only introduced in order to consider the full subcategory
`FibrantObject`. Otherwise, the typeclass `IsFibrant`
is preferred.) -/
def fibrantObjects : ObjectProperty C := fun X ↦ IsFibrant X

end Fibrant
end HomotopicalAlgebra
end
