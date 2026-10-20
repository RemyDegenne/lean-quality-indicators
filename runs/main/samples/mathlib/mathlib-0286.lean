@[expose] public section

section p_series

namespace Real

open Filter

theorem summable_one_div_nat_pow {p : ℕ} :
    Summable (fun n => 1 / (n : ℝ) ^ p : ℕ → ℝ) ↔ 1 < p := by
  simp only [one_div, Real.summable_nat_pow_inv]

end Real
end p_series
end
