namespace OAI

namespace SKGap.GaussianHistory

open MeasureTheory ProbabilityTheory Real Set Filter

open scoped BigOperators ENNReal NNReal

open GaussianStep

noncomputable section

variable {n : ℕ}

lemma squarePrior_density (p : Prior n) (f : Spin n→ℝ) (hf : 0<avg p (fun x => (f x)^2))
    (t : ℝ) {k : ℕ} (h : History n k) :
    density (squarePrior p f hf) t h =
      density p t h*avg (posterior p t h) (fun x => (f x)^2)/avg p (fun x => (f x)^2) := by
  rw [posterior_avg_weight]
  unfold density squarePrior
  dsimp
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

end
end SKGap.GaussianHistory
end OAI
