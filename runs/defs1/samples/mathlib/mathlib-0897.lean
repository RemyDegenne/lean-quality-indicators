@[expose] public section

open scoped NNReal

variable {𝕜 𝕜₂ E Eₗ F Fₗ : Type*}

namespace LinearMap

section extendOfIsometry

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂]
  [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup Eₗ] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ]
  [NormedAddCommGroup F] [Module 𝕜₂ F] [IsBoundedSMul 𝕜₂ F] [CompleteSpace F]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ₁₂] F) {e : E →ₗ[𝕜] Eₗ}

/-- Extend a linear map `f : E →ₛₗ[σ₁₂] F` to a linear isometry `Eₗ →ₛₗᵢ[σ₁₂] F` between
Banach spaces, using a dense linear map `e : E →ₗ[𝕜] Eₗ` together with the norm equality
`‖f x‖ = ‖e x‖` for all `x : E`. -/
def extendOfIsometry (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) :
    Eₗ →ₛₗᵢ[σ₁₂] F where
  toLinearMap := f.extendOfNorm e
  norm_map' := by
    refine h_dense.induction ?_ (isClosed_eq (by fun_prop) continuous_norm)
    rintro x ⟨y, rfl⟩
    norm_cast
    rw [LinearMap.extendOfNorm_eq h_dense (by use 1; simp [h_norm]), h_norm y]

end extendOfIsometry
end LinearMap
end
