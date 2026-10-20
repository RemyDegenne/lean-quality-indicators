@[expose] public section

namespace TauCeti

namespace DavisKahan

namespace ExactSinTheta

open scoped InnerProductSpace ENNReal

open TauCeti.HilbertSchmidt

noncomputable section

universe vE vF

variable {E : Type vE} {F : Type vF}

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem norm_hilbertSchmidtTensor (A : F →L[ℂ] E)
    (hA : approximationNumberEnergy A ≠ ⊤) :
    ‖hilbertSchmidtTensor A hA‖ = ContinuousLinearMap.hilbertSchmidtNorm A := by
  have hsq := norm_sq_eq_tsum_norm_column_sq (hSBasis F) (hilbertSchmidtTensor A hA)
  rw [toOperator_hilbertSchmidtTensor] at hsq
  rw [hilbertSchmidtNorm_eq_sqrt_tsum_basis (hSBasis F) A hA, ← hsq,
    Real.sqrt_sq (norm_nonneg _)]

end
end ExactSinTheta
end DavisKahan
end TauCeti
end
