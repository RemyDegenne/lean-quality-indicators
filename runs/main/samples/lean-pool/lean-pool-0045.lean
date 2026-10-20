@[expose] public section

open TauCeti.DavisKahan.Angle

open TauCeti.DavisKahan.Sylvester

namespace TauCeti

namespace DavisKahanExt

open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]

variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

theorem le_riccati_small_root_of_quadratic
    {b d t : ℝ}
    (hb : 0 ≤ b) (hd : 0 < d) (hsmall : 2 * b < d)
    (ht1 : t < 1)
    (hquad : d * t ≤ b * (1 + t ^ 2)) :
    t ≤ 2 * b / (d + Real.sqrt (d ^ 2 - 4 * b ^ 2)) := by
  have hsumpos : 0 < d + 2 * b := by
    nlinarith
  have hdiscpos : 0 < d ^ 2 - 4 * b ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr hsmall) hsumpos
    nlinarith
  have hdisc : 0 ≤ d ^ 2 - 4 * b ^ 2 := le_of_lt hdiscpos
  let s : ℝ := Real.sqrt (d ^ 2 - 4 * b ^ 2)
  let r : ℝ := 2 * b / (d + s)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = d ^ 2 - 4 * b ^ 2 := by
    dsimp [s]
    exact Real.sq_sqrt hdisc
  have hden : 0 < d + s := by
    linarith
  have hr1 : r < 1 := by
    dsimp [r]
    apply (div_lt_one hden).2
    linarith
  have hroot : b * (1 + r ^ 2) = d * r := by
    dsimp [r]
    field_simp [ne_of_gt hden]
    nlinarith [hs2]
  by_contra hnot
  have hrt : r < t := lt_of_not_ge hnot
  have hsum : t + r < 2 := by
    linarith
  have hcoef : b * (t + r) - d < 0 := by
    have hmul : b * (t + r) ≤ b * 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hsum) hb
    nlinarith
  have hfactor :
      b * (1 + t ^ 2) - d * t =
        (b * (1 + r ^ 2) - d * r) +
          (t - r) * (b * (t + r) - d) := by
    ring
  have hprod : (t - r) * (b * (t + r) - d) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hrt) hcoef
  have hneg : b * (1 + t ^ 2) - d * t < 0 := by
    rw [hfactor]
    nlinarith [hroot, hprod]
  nlinarith

end DavisKahanExt
end TauCeti
end
