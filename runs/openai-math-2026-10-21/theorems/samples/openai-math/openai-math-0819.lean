namespace OAI

section

namespace BinaryMatching

noncomputable section

open Finset MatchingEntropy

variable {n : ℕ}

lemma cut_bound {z : Pair n → ℝ} {b : ℝ} (hb : 0≤b) (hz : ∀ e, |z e|≤b)
    (S : Finset (Fin n)) : |(completeGraph n).cutMass z S|≤Fintype.card (Pair n)*b := by
  calc
    _ ≤ ∑ e∈(completeGraph n).cut S, |z e| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e∈(completeGraph n).cut S, b := sum_le_sum (fun e _ => hz e)
    _ = ((completeGraph n).cut S).card*b := by simp
    _ ≤ Fintype.card (Pair n)*b := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ _) hb

end
end BinaryMatching
end
end OAI
