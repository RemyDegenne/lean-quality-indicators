@[expose] public section

open Filter Topology Finset

namespace Zeta5Irrational

/-- Rational factor paired with `F4` in the Hermite integral formula. -/
noncomputable def g0 (a y : ℝ) : ℝ :=
  y ^ 5 / (12 * (y ^ 2 + a ^ 2))

end Zeta5Irrational
end
