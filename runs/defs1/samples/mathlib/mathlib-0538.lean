@[expose] public section

namespace CategoryTheory

open Limits

variable (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

open Pretriangulated

namespace TStructure

attribute [instance] le_isClosedUnderIsomorphisms ge_isClosedUnderIsomorphisms

variable {C}

variable (t : TStructure C)

/-- The full subcategory consisting of `t`-bounded below objects. -/
def plus : ObjectProperty C := fun X ↦ ∃ (n : ℤ), t.IsGE X n

end TStructure
end Triangulated
end CategoryTheory
end
