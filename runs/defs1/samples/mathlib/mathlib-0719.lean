@[expose] public section

universe u

open CategoryTheory MonoidalCategory Simplicial SimplicialObject.Truncated
  CartesianMonoidalCategory Limits

namespace SSet

namespace Truncated

namespace HomotopyCategory

namespace BinaryProduct

variable {X X' Y Y' Z : Truncated.{u} 2}

variable (X Y) in
/-- The functor `X.HomotopyCategory × Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
def inverse : X.HomotopyCategory × Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory :=
  Functor.uncurry.obj (curriedInverse X Y)

end BinaryProduct
end HomotopyCategory
end Truncated
end SSet
end
