public section

open MeasureTheory Polynomial Set

open scoped ENNReal

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℝ)

/-- The **real period** `Ω(W)` of a Weierstrass curve over `ℝ`, defined as twice the real value of
`WeierstrassCurve.realPeriodLIntegral`. When that integral is finite, for instance for an elliptic
curve (`WeierstrassCurve.ofReal_realPeriod`), this is `Ω(W) = 2 ∫_{Ψ₂Sq(x) > 0} dx / √Ψ₂Sq(x)`;
when it diverges, `Ω(W) = 0`. The motivation is that this integral computes `∫ |ω|` over the real
points, `ω = dx / (2y + a₁x + a₃)` being the invariant differential and the factor `2` counting the
two real points over each `x`. -/
noncomputable def realPeriod : ℝ :=
  2 * W.realPeriodLIntegral.toReal

end WeierstrassCurve
end
