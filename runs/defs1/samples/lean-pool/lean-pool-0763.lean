@[expose] public noncomputable section

open MeasureTheory

open Filter Set

open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- The integral of the right-derivative increment is locally modeled by the integral of the
linearized derivative increment. This is the estimate supplied by differentiability of
`rightDeriv f` once interval-integral bounds are available. -/
def HasRightDerivIntegralLinearizationAt (f : ℝ → ℝ) (x q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ z in nhds 0,
      ‖(∫ t in x..x + z, rightDeriv f t - rightDeriv f x) -
        ∫ t in x..x + z, q * (t - x)‖ ≤ ε * ‖z‖ ^ 2

end AleksandrovDifferentiability
end
