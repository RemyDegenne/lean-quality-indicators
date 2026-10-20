@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable {D : Type u}

section GradedComm

theorem chainBdeg_eqToHom_cast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    {p₀ q₀ p₀' q₀' : ℕ} (hp : p₀ = p₀') (hq : q₀ = q₀') :
    eqToHom (congrArg₂ (chainBdeg A M M' d) hp hq) =
      chainBdegCast A M M' d hp hq := by
  subst hp hq
  rfl

end GradedComm
end RS
end
