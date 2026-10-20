@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable {D : Type u}

section TripleIso

lemma tripleInvCover_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] (X : Mod D A) (Y : Mod D A) (Z : Mod D A) :
    (modTensorLegM A X Y ▷ Z.X) ≫ tripleInvCover A X Y Z =
      (modTensorLegN A X Y ▷ Z.X) ≫ tripleInvCover A X Y Z := by
  have hrel := modMulti_rel A [] X Y [Z]
    (rfl : [X, Y, Z] = [] ++ X :: Y :: [Z])
  rw [modMultiLegM, modMultiLegN] at hrel
  rw [tripleInvCover,
    tripleLegFst_resolveInv_assoc A X Y Z _
      (Eq.symm (rfl : [X, Y, Z] = [] ++ X :: Y :: [Z])),
    tripleLegFst_resolveInv_assoc A X Y Z _
      (Eq.symm (rfl : [X, Y, Z] = [] ++ X :: Y :: [Z])),
    hrel]

end TripleIso
end RS
end
