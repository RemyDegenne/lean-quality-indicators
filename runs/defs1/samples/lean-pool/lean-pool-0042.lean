@[expose] public section

open Finset

namespace Zeta5Irrational

/-- The additive error of the table bound. -/
noncomputable def Ctab (n p : ℕ) (k : ℤ) : ℝ :=
  5 * ∑ i, ∑ j, |bIn (40 * n / p) (3 * n / p) k i j| +
        ((ktopI n p - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) +
      2 * Bmax n p +
    1

end Zeta5Irrational
end
