@[expose] public section

noncomputable section

namespace NavierStokes.GaussianTailFlat

open Set Filter Function

open scoped ContDiff Topology BigOperators

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

open WeightedClasses

/-- Only the actual scale identity and a polynomial slow-scale upper bound
are used. The exponent may be any real number. -/
structure BandScaleControl (s : StripData D) where
  /-- Power of `BandScaleControl`, of type `ℝ`. -/
  power : ℝ
  epsilon_eq : ∀ n, s.epsilon n = ChartScales.Q n ^ power
  /-- Bound constant of `BandScaleControl`, of type `ℝ`. -/
  boundConstant : ℝ
  constant_one_le : 1 ≤ boundConstant
  /-- Degree of `BandScaleControl`, of type `ℕ`. -/
  degree : ℕ
  slow_le : ∀ n, s.slow n ≤ boundConstant * (1 + ChartScales.S n) ^ degree

end NavierStokes.GaussianTailFlat
end
end
