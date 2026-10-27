@[expose] public section

open Zeta32.Arith.Local

open Polynomial

open scoped BigOperators

namespace Zeta32.Outer

noncomputable section

export Zeta32.Arith.Small (D_succ D_eq_desc D_monic D_natDegree
  descPochhammer_eval_neg_one D_eval_eq_prod)

/-- The integral polynomial with roots `-1`, …, `-m`. -/
def integerD (m : ℕ) : ℤ[X] := ∏ j ∈ Finset.Icc 1 m, (X + C (j:ℤ))

end
end Zeta32.Outer
end
