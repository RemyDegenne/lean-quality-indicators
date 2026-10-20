@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable {D : Type u}

theorem chainDelta2_chainBdegι
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (p₀ q₀ k : ℕ) :
    chainDelta2 A M M' d (p₀ + k) (q₀ + k) ≫
        chainBdegι A M M' d p₀ q₀ (k + 1) =
      chainBdegι A M M' d p₀ q₀ k :=
  delta_chainColimitι
    (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
    (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k)) k

end RS
end
