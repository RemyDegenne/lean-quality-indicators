namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

namespace SphericalPerceptronFreeEnergy

lemma enrichedIncrementFactors_exact {N k : ℕ} (p d : Fin N→ℕ) (h : Fin (k+1)→ℝ) :
    (fun j => diagonalMark (enrichedIncrementFactors p d h j))=enrichedIncrementMap p d h := by
  funext j
  simp only [enrichedIncrementFactors,enrichedIncrementMap]
  split_ifs
  · rfl
  · ext x i
    change 0*x i=0
    ring

end SphericalPerceptronFreeEnergy
end
end OAI
