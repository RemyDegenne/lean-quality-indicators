@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable {D : Type u}

section CrossStep

/-- The step bridge: braid the monoid over the tail of the first
block and retype at the relation window of the head slot. -/
def modCrossStepBridge [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    (X P : Mod D A) (l' Ys : List (Mod D A)) :
    (pre : List (Mod D A)) →
      modCrossMid A (X :: P :: l') Ys pre ⟶
        modMultiMid A pre X P (l' ++ Ys)
  | [] =>
    (((α_ X.X (P.X ⊗ modList A l') A).hom ≫
        (X.X ◁ (β_ (P.X ⊗ modList A l') A).hom) ≫
        (α_ X.X A (P.X ⊗ modList A l')).inv) ▷ modList A Ys) ≫
      (α_ (X.X ⊗ A) (P.X ⊗ modList A l') (modList A Ys)).hom ≫
      ((X.X ⊗ A) ◁
        (α_ P.X (modList A l') (modList A Ys)).hom) ≫
      ((X.X ⊗ A) ◁ (P.X ◁ (modListConcat A l' Ys).hom)) ≫
      (α_ (X.X ⊗ A) P.X (modList A (l' ++ Ys))).inv
  | Q :: rest => Q.X ◁ modCrossStepBridge A X P l' Ys rest

end CrossStep
end RS
end
