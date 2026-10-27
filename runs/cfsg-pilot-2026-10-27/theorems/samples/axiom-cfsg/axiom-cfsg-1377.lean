namespace CFSG.FeitThompson

public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace OrderedFieldPairEstimates

open Subgroup Finset

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.FeitThompson.Prep05

open CFSG.FeitThompson.PairedFullSupportFieldAction

universe u

variable {G : Type u} [Group G]

theorem cast_geomSumDiv {K : Type*} [Field K] [CharZero K] {r : ℕ} (hr : 2 ≤ r) (n : ℕ) :
    (((r ^ n - 1) / (r - 1) : ℕ) : K) = ((r : K) ^ n - 1) / ((r : K) - 1) := by
  have hne : (r : K) - 1 ≠ 0 := by
    have h : (r : K) ≠ 1 := by exact_mod_cast (show r ≠ 1 by omega)
    exact sub_ne_zero_of_ne h
  rw [← sum_range_pow_eq_div hr]
  push_cast
  rw [← geom_sum_mul (r : K) n, mul_div_assoc, div_self hne, mul_one]

end OrderedFieldPairEstimates
end
end CFSG.FeitThompson
