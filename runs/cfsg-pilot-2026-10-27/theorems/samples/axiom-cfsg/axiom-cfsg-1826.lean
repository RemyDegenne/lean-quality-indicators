public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614DOG

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)

theorem eq_one_of_conj_eq_inv_of_isPGroup {Y : Type*} [Group Y] (hY : IsPGroup 3 Y) {a b : Y}
    (hb3 : b ^ 3 = 1) (hab : a * b * a⁻¹ = b⁻¹) : b = 1 := by
  obtain ⟨k, hk⟩ := hY a
  have ha2 : a ^ 2 * b = b * a ^ 2 := by
    have h1 : a * b⁻¹ * a⁻¹ = b := by
      rw [show a * b⁻¹ * a⁻¹ = (a * b * a⁻¹)⁻¹ by group, hab, inv_inv]
    rw [sq]
    calc a * a * b = a * (a * b * a⁻¹) * a := by group
      _ = a * b⁻¹ * a := by rw [hab]
      _ = (a * b⁻¹ * a⁻¹) * (a * a) := by group
      _ = b * (a * a) := by rw [h1]
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨m, hm⟩ := hodd
  have ha : a = (a ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = 3 ^ k + 1 by omega, pow_succ, hk, one_mul]
  have hcomm : a * b = b * a := by
    rw [ha]
    exact ((Commute.pow_left (show Commute (a ^ 2) b from ha2) (m + 1)))
  have hbb : b = b⁻¹ := by
    rw [← hab, hcomm, mul_inv_cancel_right]
  have hb2 : b ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [hbb]
    exact mul_inv_cancel b
  calc b = b ^ 3 * (b ^ 2)⁻¹ := by group
    _ = 1 := by rw [hb3, hb2]; group

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614DOG
end
