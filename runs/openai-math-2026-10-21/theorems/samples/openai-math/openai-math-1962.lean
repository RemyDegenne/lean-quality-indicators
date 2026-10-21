namespace OAI

namespace TwoPointCorrelations

open Finset

open scoped Classical

lemma mrt_short_sum_blocks (F : ℕ → ℂ) (h K v : ℕ) (α : ℝ) :
    shortExponentialSum F (K*h) α v =
      ∑ j ∈ range K, shortExponentialSum F h α (v+j*h:ℕ) := by
  induction K with
  | zero =>
    simp only [zero_mul, shortExponentialSum_at_nat, sum_Icc_shift, sum_range_zero]
  | succ K ih =>
    rw [show (K+1)*h = K*h+h by ring, mrt_short_sum_append, ih, sum_range_succ]

end TwoPointCorrelations
end OAI
