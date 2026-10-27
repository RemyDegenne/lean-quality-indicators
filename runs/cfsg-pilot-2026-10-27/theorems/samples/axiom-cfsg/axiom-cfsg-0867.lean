public section

namespace CFSG.GH74.Uniqueness.Bender

theorem three_dvd_linear_card (m : ℕ) :
    3 ∣ ((2 ^ m) ^ 1 + 1) * ((2 ^ m) ^ 1 * ((2 ^ m - 1) * 1)) := by
  have hmod : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
    have : ¬ 3 ∣ 2 ^ m := fun hd => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
      omega
    omega
  rcases hmod with hm | hm
  · have hd : 3 ∣ 2 ^ m - 1 := by omega
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right hd 1) _) _
  · have hd : 3 ∣ 2 ^ m + 1 := by omega
    exact Dvd.dvd.mul_right (by rwa [pow_one]) _

end CFSG.GH74.Uniqueness.Bender
end
