@[expose] public section

open CauSeq Finset IsAbsoluteValue

open scoped ComplexConjugate

namespace Real

open Complex

variable (x y : ℝ)

open IsAbsoluteValue Nat

@[mono, gcongr]
theorem exp_strictMono : StrictMono exp := fun x y h => by
  rw [← sub_add_cancel y x, Real.exp_add]
  exact (lt_mul_iff_one_lt_left (exp_pos _)).2
      (lt_of_lt_of_le (by linarith) (add_one_le_exp_of_nonneg (by linarith)))

end Real
end
