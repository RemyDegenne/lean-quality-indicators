@[expose] public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

variable (hm : 2 * m + 1 = p) (n : ℕ)

/-- Tail poles `N < j ≤ K`. -/
def tailO (n : ℕ) : Finset ℕ :=
  Icc (3 * n + 1) (40 * n)

end Zeta5Irrational
end
