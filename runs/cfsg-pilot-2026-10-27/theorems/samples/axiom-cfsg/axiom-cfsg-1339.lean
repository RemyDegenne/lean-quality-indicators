public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1523Res3

open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem not_cube_dvd_small {n q : ℕ} (hn : n = 4 ∨ n = 6 ∨ n = 8) (hq : 2 ≤ q) :
    ¬ q ^ 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have hcheck : ∀ r < 41, 2 ≤ r → ¬ r ^ 3 ∣ 255 ∧ ¬ r ^ 3 ∣ 4095 ∧ ¬ r ^ 3 ∣ 65535 := by
    decide
  intro hd
  have hM : (2 ^ n) ^ 2 - 1 ≤ 65535 := by
    rcases hn with rfl | rfl | rfl <;> norm_num
  have hpos : 0 < (2 ^ n) ^ 2 - 1 := by
    rcases hn with rfl | rfl | rfl <;> norm_num
  have hq41 : q < 41 := by
    by_contra h
    have h1 : 41 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (not_lt.mp h) 3
    have h2 := Nat.le_of_dvd hpos hd
    omega
  obtain ⟨h4, h6, h8⟩ := hcheck q hq41 hq
  rcases hn with rfl | rfl | rfl
  · exact h4 (by simpa using hd)
  · exact h6 (by simpa using hd)
  · exact h8 (by simpa using hd)

end CFSG.RankThree.PartTwo.Sec15.Proof1523Res3
end
