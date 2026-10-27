@[expose] public section

namespace TauCeti

open TauCeti

open scoped InnerProductSpace BigOperators ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- An integrable scalar Fourier kernel representing the reciprocal function
outside the unit interval, with controlled `L¹` mass. -/
def HasIntegrableReciprocalFourierKernel (mass : ℝ) : Prop :=
  ∃ f : ℝ → ℂ,
    Measurable f ∧
    MeasureTheory.Integrable f ∧
    (∀ x : ℝ, 1 ≤ |x| →
      (∫ t, f t * Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
        (1 : ℂ) / (x : ℂ)) ∧
    (∫ t, ‖f t‖) ≤ mass

end TauCeti
end
