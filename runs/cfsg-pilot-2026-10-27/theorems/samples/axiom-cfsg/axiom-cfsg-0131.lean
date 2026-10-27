public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open Matrix MatrixGroups CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE

open CFSG.RankThree.E6 (chainRoot)

theorem chainRoot_e8a4chain_eq (i j : Fin 5) :
    chainRoot e8a4chain i j = ∑ k : Fin 4, ((if (i : ℕ) ≤ k ∧ (k : ℕ) < j then 1 else 0) -
      (if (j : ℕ) ≤ k ∧ (k : ℕ) < i then 1 else 0) : ℤ) • e8s k := by
  funext l
  simp only [chainRoot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : e8s k = Pi.single (e8a4chain k) 1 := by
    fin_cases k <;> rfl
  rw [h1, Pi.single_apply]
  simp [eq_comm]

end CFSG.HardMathSupport.Timmesfeld.Torality
end
