public section

namespace TauCeti

open MeasureTheory Polynomial TauCeti.Probability ProbabilityTheory

variable (𝕜 : Type*) [RCLike 𝕜] (ι : Type*) [Fintype ι]

/-- **The multivariate Gaussian Hermite basis.** `piHilbertBasis` over the one-dimensional Gaussian
Hermite basis in every coordinate. -/
noncomputable def gaussianHermitePiBasis :
    HilbertBasis (ι → ℕ) 𝕜 (Lp 𝕜 2 (Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ))) :=
  piHilbertBasis fun _ => gaussianHermiteHilbertBasis 𝕜

end TauCeti
end
