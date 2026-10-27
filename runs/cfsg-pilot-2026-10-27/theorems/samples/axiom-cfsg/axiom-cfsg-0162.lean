public section

namespace CFSG.RankThree.PartOne.KFBloom

open CFSG.ComponentClassification

theorem not_dvd_360 {p : ℕ} (hp : p.Prime) (h : 7 ≤ p) : ¬ p ∣ 360 := by
  intro hd
  have h360 : (360 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 := by norm_num
  rw [h360] at hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
  · have := Nat.le_of_dvd (by norm_num) h1
    omega

end CFSG.RankThree.PartOne.KFBloom
end
