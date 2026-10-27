@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

section

variable [IsTriangulated C]

section

variable (a b : EInt)

/-- The natural transformation from
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b` to
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a`. (This is an isomorphism.) -/
@[simps!]
noncomputable def eTruncLTGELTSelfToGELT :
    t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ⟶
      t.eTruncLT.obj b ⋙ t.eTruncGE.obj a :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerLeft _ (t.eTruncLTι b) ≫
    (Functor.rightUnitor _).hom

end
end
end TStructure
end Triangulated
end CategoryTheory
end
