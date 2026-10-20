@[expose] public section

open Filter

open scoped Topology

namespace Real

section UpperSequence

lemma eulerMascheroniSeq'_six_lt_two_thirds : eulerMascheroniSeq' 6 < 2 / 3 := by
  have h1 : eulerMascheroniSeq' 6 = 49 / 20 - log 6 := by
    rw [eulerMascheroniSeq']
    norm_num
  rw [h1, sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', lt_log_iff_exp_lt (by positivity)]
  norm_num
  have := rpow_lt_rpow (exp_pos _).le exp_one_lt_d9 (by simp : (0 : ℝ) < 107 / 60)
  rw [exp_one_rpow] at this
  refine lt_trans this ?_
  rw [← rpow_lt_rpow_iff (z := 60), ← rpow_mul, div_mul_cancel₀, ← Nat.cast_ofNat,
    ← Nat.cast_ofNat, rpow_natCast, Nat.cast_ofNat, ← Nat.cast_ofNat (n := 60), rpow_natCast]
  · norm_num
  all_goals positivity

end UpperSequence
end Real
end
