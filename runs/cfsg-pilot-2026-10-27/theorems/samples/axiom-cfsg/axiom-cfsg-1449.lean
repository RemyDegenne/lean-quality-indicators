public section

namespace CFSG.StandardType

namespace IOneU

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2 TableBUE

section Arith

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem suCard_gt_of_five_le (h : UnitaryFieldData 2 n K) (hn : n = 1) {m : ℕ} (hm : 5 ≤ m) :
    25920 < Nat.card ↥(unitarySU 2 n K m) := by
  refine lt_of_lt_of_le ?_ (card_su_le_of_le h hm)
  have h5 := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h (n := 5) (by norm_num)
  subst hn
  have e : Finset.Icc 2 5 = ({2, 3, 4, 5} : Finset ℕ) := by decide
  rw [e] at h5
  norm_num [Finset.prod_insert] at h5
  have h7 : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSU 5 2 K) = 13685760 := by
    exact_mod_cast h5
  rw [show unitarySU 2 1 K 5 = CFSG.Assembly.LowTwoRank.StatedSU 5 2 K from rfl, h7]
  norm_num

end Arith
end IOneU
end CFSG.StandardType
end
