public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB TauCeti

open CFSG.RankThree.PartTwo

theorem lieSOutOrd_sp6two : LieSOutOrd 1451520 where
  three_dvd := by norm_num
  not_dvd_216 := by norm_num
  not_dvd_360 := by norm_num
  not_dvd_12096 := by norm_num
  not_dvd_17971200 := by norm_num
  ne_triD4 := fun Q hQ => by
    rcases (by omega : Q = 2 ∨ Q = 3 ∨ 4 ≤ Q) with rfl | rfl | h4
    · norm_num
    · norm_num
    · exact ne_of_lt (lt_of_lt_of_le (by norm_num) (lieSOut_triD4_order_ge h4))
  ne_g2 := fun Q hQ => by
    rcases (by omega : Q = 4 ∨ 5 ≤ Q) with rfl | h5
    · norm_num
    · exact ne_of_lt (lt_of_lt_of_le (by norm_num) (lieSOut_g2_order_ge h5))
  ne_sl3 := KFacts.KS14.forall_of_forall_lt (B := 114) (by norm_num) (by norm_num)
    (by decide +kernel)
  ne_su3 := KFacts.KS14.forall_of_forall_lt (B := 114) (by norm_num) (by norm_num)
    (by decide +kernel)

end CFSG.LocalAnalysis.GLTheoremA.H1431c
end
