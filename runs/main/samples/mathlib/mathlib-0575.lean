@[expose] public section

open Function Set Topology

variable {R R₂ R₃ E E₂ E₃ F 𝓕 : Type*} [Semiring R] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} {σ₁₃ : R →+* R₃} {σ₃₁ : R₃ →+* R}
  {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃] [RingHomInvPair σ₂₃ σ₃₂]
  [RingHomInvPair σ₃₂ σ₂₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [SeminormedAddCommGroup E₃]
  [Module R E] [Module R₂ E₂] [Module R₃ E₃]
  [NormedAddCommGroup F] [Module R F]

@[inherit_doc]
notation:25 E " →ₛₗᵢ[" σ₁₂:25 "] " E₂:0 => LinearIsometry σ₁₂ E E₂

notation:25 E " →ₗᵢ[" R:25 "] " E₂:0 => LinearIsometry (RingHom.id R) E E₂

notation:25 E " →ₗᵢ⋆[" R:25 "] " E₂:0 => LinearIsometry (starRingEnd R) E E₂

namespace LinearIsometry

variable (f : E →ₛₗᵢ[σ₁₂] E₂) (f₁ : F →ₛₗᵢ[σ₁₂] E₂)

variable [FunLike 𝓕 E E₂]

@[simp]
theorem preimage_sphere (x : E) (r : ℝ) : f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r :=
  f.isometry.preimage_sphere x r

end LinearIsometry
end
