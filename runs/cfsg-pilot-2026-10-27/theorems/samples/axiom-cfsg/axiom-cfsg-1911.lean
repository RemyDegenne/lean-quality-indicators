public section

namespace CFSG.Quasithin.Ch1Two

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.VolI

open CFSG.Quasithin.Ch1Four CFSG.Assembly.LowTwoRank

section Cases

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}

theorem false_of_rank2
    (hBL : B ≤ L) (hA : A38Types ↥L) {n : ℕ}
    (hn : IsPSL 2 2 n (ModO2 B)) (hR : IsRank2LieChar2 ↥L) : False := by
  have hcard := card_eq_168_of_rank2 hA hR
  obtain ⟨h2, hc⟩ := card_of_isPSL_two_two hn
  obtain ⟨j, hj⟩ := card_modO2_mul (H := ↥B)
  have hdvd : Nat.card ↥B ∣ 168 := hcard ▸ Subgroup.card_dvd_of_le hBL
  rw [← hj, hc] at hdvd
  have h4 : 4 ^ n - 1 ∣ 168 := (Dvd.intro (2 ^ n * 2 ^ j) (by ring)).trans hdvd
  have hle : 4 ^ n - 1 ≤ 168 := Nat.le_of_dvd (by norm_num) h4
  have hn3 : n ≤ 3 := by
    by_contra hgt
    have : 4 ^ 4 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n <;> norm_num at h4

end Cases
end CFSG.Quasithin.Ch1Two
end
