public section

noncomputable section

open Filter Set

open scoped Nat Topology

namespace Real

/-- The modified Bessel function of the first kind `I_ν(x)` of real order `ν` at a real argument
`x`: the real part of `(x / 2) ^ ν * ₀F₁(; ν + 1; (x / 2) ^ 2)`, with the complex power and the
regularized hypergeometric function `₀F₁`. -/
@[pp_nodot]
def besselI (ν x : ℝ) : ℝ :=
  (((x : ℂ) / 2) ^ (ν : ℂ) * Complex.regularizedHGFun 0 {(ν : ℂ) + 1} (((x : ℂ) / 2) ^ 2)).re

end Real
end
end
