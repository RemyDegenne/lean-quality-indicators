public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

open CFSG.Quasithin.H13.U4Par

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

variable {m : ℕ} {K : Type} [Field K]

theorem lv_coe_pow_diag (h : UnitaryFieldData 2 m K) (g : hypSU h 2 0) (d : Ix → K)
    (hg : ((g : GL Ix K) : Matrix Ix Ix K) = diagonal d) (n : ℕ) :
    (((g ^ n : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = diagonal (fun i => d i ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, Subgroup.coe_one, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    simp
  | succ n ih =>
    rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ih, hg, diagonal_mul_diagonal]
    congr 1
    funext i
    simp [pow_succ]

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
end
