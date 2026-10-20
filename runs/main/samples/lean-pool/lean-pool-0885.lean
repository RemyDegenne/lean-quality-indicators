@[expose] public section

open Complex Filter Function MeasureTheory Metric Set

open scoped ENNReal NNReal Real Topology

namespace CarlsonFunctions.SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma torusMap_mem_closedPolydisc {n : ℕ} {c : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (θ : Fin n → ℝ) : torusMap c (fun _ => R) θ ∈ closedPolydisc c R := by
  intro i _
  simp [torusMap, mem_closedBall, dist_eq_norm, abs_of_nonneg hR]

end CarlsonFunctions.SeveralComplexVariables
end
