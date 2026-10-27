public section

namespace CFSG.Quasithin.H13.L829NK.U3Out

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {p : ℕ} {K : Type} [Field K]

theorem wM00 : wM 0 0 = (0 : K) := by simp [wM]

end CFSG.Quasithin.H13.L829NK.U3Out
end
