@[expose] public section

noncomputable section

open Filter intervalIntegral Set Real MeasureTheory

open scoped Nat Topology Real

section BetaIntegral

namespace Complex

/-- The Beta function `Β (u, v)`, defined as `∫ x:ℝ in 0..1, x ^ (u - 1) * (1 - x) ^ (v - 1)`. -/
noncomputable def betaIntegral (u v : ℂ) : ℂ :=
  ∫ x : ℝ in 0..1, (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)

end Complex
end BetaIntegral
end
end
