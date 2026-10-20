namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_eq_finiteIdeleDiagonal_mul_mul_of_ne

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.style.multiGoal false

set_option linter.unusedSimpArgs false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField

noncomputable section

namespace P2mNormalize

section Coord

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

variable (a b)

variable {a b}

theorem locNrd_finiteIdeleDiagonal {w : HeightOneSpectrum (𝓞 ℚ)}
    {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ) (γ : (ℍ[ℚ, a, b])ˣ) :
    locNrd a b w φ ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)
      = algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b])) := by
  rw [Submodule.val_finiteIdeleDiagonal_apply, locNrd_diagonal hφ]

end Coord
end P2mNormalize
end
end P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_eq_finiteIdeleDiagonal_mul_mul_of_ne
