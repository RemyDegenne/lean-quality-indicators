@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable {D : Type u}

theorem powCopairA_unit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (n : ℕ) :
    η[A] ≫ powCopairA A M M' d n = powUnitStage A M M' d n :=
  act_on_point_unit A
    (modTensorAct A (modPowMod A M.X n) (modPowMod A M'.X n))
    (modTensorAct_one A (modPowMod A M.X n) (modPowMod A M'.X n))
    (powUnitStage A M M' d n)

end RS
end
