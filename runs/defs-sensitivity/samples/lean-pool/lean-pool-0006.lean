@[expose] public section

namespace LongGapsBetweenPrimes

noncomputable section

/-- The average of `f` over the integers in `[0, T)`. -/
def integerAverage (T : ℕ) (f : ℕ → ℝ) : ℝ := (∑ n ∈ Finset.range T, f n) / T

end
end LongGapsBetweenPrimes
end
