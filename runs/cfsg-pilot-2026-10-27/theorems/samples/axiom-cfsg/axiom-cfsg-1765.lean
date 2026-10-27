public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

theorem pow_le_of_mul_eq {k n m r : ℕ} (hm : ¬ 7 ∣ m) (h : 7 ^ k * r = 7 ^ n * m) : k ≤ n := by
  by_contra hlt
  rw [not_le] at hlt
  apply hm
  have h1 : 7 ^ n * 7 ∣ 7 ^ n * m := by
    rw [← h]
    calc 7 ^ n * 7 = 7 ^ (n + 1) := (pow_succ 7 n).symm
      _ ∣ 7 ^ k := pow_dvd_pow 7 hlt
      _ ∣ 7 ^ k * r := dvd_mul_right _ _
  exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h1

end CFSG.RankThree.PartOne.TAIL
end
