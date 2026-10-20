@[expose] public section

open Polynomial BigOperators Nat

noncomputable section

namespace Problem4

variable (n : ℕ) (hn : 2 ≤ n)

/-- Convert a coefficient sequence back to a polynomial. -/
def coeffsToPoly (a : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  (Finset.range (n + 1)).sum fun k ↦ Polynomial.C (a k) * Polynomial.X ^ (n - k)

end Problem4
end
end
