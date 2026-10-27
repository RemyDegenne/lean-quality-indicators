@[expose] public section

noncomputable section

open scoped Nat Real Interval

open Complex MeasureTheory Set intervalIntegral

local notation "𝕌" => UnitAddCircle

section BernoulliPeriodized

/-- The Bernoulli polynomial, extended from `[0, 1)` to the unit circle. -/
def periodizedBernoulli (k : ℕ) : 𝕌 → ℝ :=
  AddCircle.liftIco 1 0 (bernoulliFun k)

end BernoulliPeriodized
end
end
