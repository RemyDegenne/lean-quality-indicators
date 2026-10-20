@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

lemma isLE_truncLE_obj (X : C) (a b : ℤ) (hn : a ≤ b := by lia) :
    t.IsLE ((t.truncLE a).obj X) b :=
  t.isLE_truncLT_obj ..

end TStructure
end Triangulated
end CategoryTheory
end
