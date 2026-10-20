public section

namespace TauCeti

open FourierTransform MeasureTheory Polynomial Real

open scoped SchwartzMap

/-- The Hermite polynomial dilated to Mathlib's Fourier convention, `Hₙ(2√π · X)`. Its Gaussian
envelope `e^{-πx²}` is the self-dual Gaussian of the `e^{-2πixξ}` convention, so the resulting
`√w`-normalized functions are the `TauCeti.twoPiHermiteFunction`. -/
noncomputable def twoPiHermiteDilated (n : ℕ) : Polynomial ℝ :=
  (hermiteDilated n).comp (Polynomial.C (Real.sqrt (2 * Real.pi)) * Polynomial.X)

end TauCeti
end
