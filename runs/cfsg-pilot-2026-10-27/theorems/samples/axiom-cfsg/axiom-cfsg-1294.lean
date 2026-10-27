public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair

open CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup CFSG.Open CFSG.Assembly.LowTwoRank

open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open scoped TensorProduct MatrixGroups

theorem not_dvd_card_sl2_two_mul {q : ℕ} (hq : 8 ≤ q) :
    ¬ q * (q ^ 2 - 1) ∣ (2 * q) * ((2 * q) ^ 2 - 1) := by
  intro h
  have hQ : 64 ≤ q ^ 2 := by nlinarith
  have e1 : (2 * q) * ((2 * q) ^ 2 - 1) = q * (2 * (4 * q ^ 2 - 1)) := by
    rw [mul_pow]
    ring
  rw [e1] at h
  have h2 := Nat.dvd_of_mul_dvd_mul_left (by omega) h
  generalize q ^ 2 = Q at hQ h2
  have e2 : 2 * (4 * Q - 1) = 8 * (Q - 1) + 6 := by omega
  rw [e2] at h2
  have h3 := (Nat.dvd_add_right (dvd_mul_left (Q - 1) 8)).mp h2
  have := Nat.le_of_dvd (by norm_num) h3
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair
end
