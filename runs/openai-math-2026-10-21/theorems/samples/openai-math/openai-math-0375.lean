namespace OAI

noncomputable section

namespace HarmonicCounterexample.Angular

open MvPolynomial Matrix HarmonicCounterexample.Control

open scoped BigOperators

variable {n : ℕ} (l : ℕ)

lemma pair_swap_left (i j k r : Fin n) : planePair l j i k r= -planePair l i j k r := by
  unfold planePair
  rw [plane_swap l i j,end_neg_mul,end_trace_neg]

end HarmonicCounterexample.Angular
end
end OAI
