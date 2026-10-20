@[expose] public section

open CauSeq Finset IsAbsoluteValue

open scoped ComplexConjugate

namespace Real

open Complex Finset

theorem abs_exp_sub_one_le {x : ℝ} (hx : |x| ≤ 1) : |exp x - 1| ≤ 2 * |x| := by
  have : ‖(x : ℂ)‖ ≤ 1 := mod_cast hx
  exact_mod_cast Complex.norm_exp_sub_one_le (x := x) this

end Real
end
