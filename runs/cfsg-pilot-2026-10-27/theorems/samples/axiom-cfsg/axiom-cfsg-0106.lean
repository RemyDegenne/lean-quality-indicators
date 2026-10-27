public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem trace_diagTau {τ : K} (hτ : τ ^ 3 = 1) :
    ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = τ + τ ^ 2 + 1 := by
  rw [coe_diagTau_eq_diagonal, trace_diagonal, Fin.sum_univ_three]
  simp

end CFSG.RankThree.PartTwo.Sec4
end
