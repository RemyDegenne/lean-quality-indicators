@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Oz.OneRowExample

open Set

/-- The `n`-th positive exponent in Conway's one-row normal form. -/
def exponent (n : ℕ) : ℝ :=
  1 / (n + 1 : ℝ)

end ConwayRefinement.Standalone.Oz.OneRowExample
end
