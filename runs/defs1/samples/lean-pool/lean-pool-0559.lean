section

@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

open MeasureTheory

open scoped FourierTransform

namespace NavierStokesR3.PressureTestBounds

open ProblemStatement Comparison HarmonicTestFunctionals

/-- A finite numerical constant depending only on three-dimensional Lebesgue measure. -/
def fourierMomentConstant : ℝ :=
  Real.sqrt (∫ ξ : Space, (1 + ‖ξ‖ ^ 2)⁻¹ ^ 2)

end NavierStokesR3.PressureTestBounds
end
end
end
