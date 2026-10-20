@[expose] public section

namespace Sendov

/-- The integrand of the raw polar inequality `(1Q)`. -/
noncomputable def Ppolar (a x t : ℝ) : ℝ :=
  a ^ 2 + 2 * a * t * x * (1 - a ^ 2) + t ^ 2 * (1 - a ^ 2) ^ 2

end Sendov
end
