public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C} {P : ObjectProperty C}

namespace IsFrobeniusSubcategory

variable (hP : E.IsFrobeniusSubcategory P) (hE : E.IsFrobenius)

include hP

theorem isClosedUnderBinaryProducts : P.IsClosedUnderBinaryProducts := by
  let := hP.containsZero
  let := hP.extensionClosed.isClosedUnderIsomorphisms
  exact hP.extensionClosed.isClosedUnderBinaryProducts

end IsFrobeniusSubcategory
end TauCeti.ExactStructure
end
