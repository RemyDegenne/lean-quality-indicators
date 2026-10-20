@[expose] public section

namespace TauCeti

open TauCeti

open scoped InnerProductSpace BigOperators ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

theorem hasFiniteReciprocalFourierInterpolation_pi_div_two_add_eps_of_integrableKernel
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hgap : ∀ i j, 1 ≤ |α i - β j|) {eps : ℝ} (heps : 0 < eps)
    (hkernel : HasIntegrableReciprocalFourierKernel (Real.pi / 2)) :
    HasFiniteReciprocalFourierInterpolation
      α β 1 (Real.pi / 2 + eps) := by
  exact hasFiniteReciprocalFourierInterpolation_of_approximate
    α β hgap heps fun tolerance htolerance =>
      hasApproximateFiniteReciprocalFourierInterpolation_of_integrableKernel
        α β hgap htolerance hkernel

end TauCeti
end
