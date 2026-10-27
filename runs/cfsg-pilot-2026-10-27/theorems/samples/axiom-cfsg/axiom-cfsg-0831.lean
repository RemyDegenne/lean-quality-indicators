public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

open scoped Pointwise

theorem eq_nine_of_dvd_of_lt {n : ℕ} (h9 : 9 ∣ n) (h81 : n ∣ 81) (hlt : n < 27) : n = 9 := by
  have h0 : 0 < n := Nat.pos_of_dvd_of_pos h81 (by norm_num)
  interval_cases n <;> omega

end CFSG.Sporadic.Recognition.JankoWong
end
