set_option autoImplicit false

namespace LanglandsTunnell

open NumberField AutomorphicForm IsDedekindDomain EisensteinWeightOne FLT.ExplicitLift

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def IsAttachedExact (ρ : Γℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (π₀ : HeckeEigensystem ℚ (ℤ√(-2))) (T : Finset ℕ) : Prop :=
  ∀ p : Nat.Primes, (p : ℕ) ∉ T →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) →
      ∀ σ : Γℚ, A.IsFrobeniusAt σ (p : ℕ) →
        red (π₀.a ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p))
          = ((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
              Matrix (Fin 2) (Fin 2) (ZMod 3)).trace

end LanglandsTunnell
