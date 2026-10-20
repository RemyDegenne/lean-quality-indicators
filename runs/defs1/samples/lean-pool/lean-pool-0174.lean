@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal ComplexConjugate

namespace QuadraticCarleson

/-- The finite maximal convolution output, written using the extended norm
so its squared integral is meaningful without any prior integrability. -/
noncomputable def finiteConvolutionMaximal {N : ℕ}
    (κ : Fin N → ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ i : Fin N, ‖∫ t, κ i (x - t) * f t‖ₑ

end QuadraticCarleson
end
