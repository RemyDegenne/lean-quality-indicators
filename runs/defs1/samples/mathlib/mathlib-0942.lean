@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

section Bifibrant

variable [CategoryWithCofibrations C] [HasInitial C]
  [CategoryWithFibrations C] [HasTerminal C]

namespace BifibrantObject

/-- The inclusion functor `BifibrantObject C ⥤ FibrantObject C`. -/
abbrev ιFibrantObject : BifibrantObject C ⥤ FibrantObject C :=
  ObjectProperty.ιOfLE (bifibrantObjects_le_fibrantObject C)

end BifibrantObject
end Bifibrant
end HomotopicalAlgebra
end
