public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryCoord

section Orders

open CFSG.Open CFSG.Timmesfeld.ClassicalOrders

theorem eq_of_two_pow_mul_eq_of_odd {f g m n : ℕ} (hm : Odd m) (hn : Odd n)
    (h : 2 ^ f * m = 2 ^ g * n) : f = g := by
  have h1 : f ≤ g := by
    have h' : 2 ^ f ∣ 2 ^ g * n := ⟨m, h.symm⟩
    have := (Nat.Coprime.pow_left f (Nat.coprime_two_left.mpr hn)).dvd_of_dvd_mul_right h'
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have h2 : g ≤ f := by
    have h' : 2 ^ g ∣ 2 ^ f * m := ⟨n, h⟩
    have := (Nat.Coprime.pow_left g (Nat.coprime_two_left.mpr hm)).dvd_of_dvd_mul_right h'
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  omega

end Orders
end CFSG.RankThree.PartOne.KFU
end
