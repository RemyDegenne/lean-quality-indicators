public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

open CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG.Assembly.RankThreeEven (projImage projSL projSU projSp)

open CFSG.Open (StatedSL StatedSp)

open Matrix

section Rows

theorem kT2_seven_Sp4 (n : ℕ) (hn : 1 ≤ n) : RowOf425 (projSp 2 (GaloisField 2 n)) := by
  refine kT2_Sp4 ?_
  rw [GaloisField.card 2 n (by omega)]
  intro h3
  have := Nat.prime_three.dvd_of_dvd_pow h3
  omega

end Rows
end CFSG.RankThree.PartTwo.Sec4.Ronan148L
end
