universe v u

namespace CategoryTheory

open Limits Pretriangulated ZeroObject

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

public section

/-- The natural transformation `𝟭 C ⟶ t.truncGE n` when `t` is a t-structure
on a category `C` and `n : ℤ`. -/
noncomputable def truncGEπ (n : ℤ) : 𝟭 _ ⟶ t.truncGE n :=
  Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₂Toπ₃

end
end TStructure
end Triangulated
end CategoryTheory
