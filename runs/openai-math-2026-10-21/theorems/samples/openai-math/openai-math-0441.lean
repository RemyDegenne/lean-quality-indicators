namespace OAI

open Erdos970

namespace Ostmann.Preliminaries

open Real Finset MeasureTheory

open scoped BigOperators

lemma sum_primeLogWeight_le {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogWeight n) ≤
      Real.log x + (Real.log 4 + 4) := by
  have h := (abs_le.mp (Erdos970.Mertens.sum_log_prime_div_eq_log hx)).2
  rw [sum_primeLogWeight]
  linarith

end Ostmann.Preliminaries
end OAI
