@[expose] public section

namespace FelsConjectureProof

lemma binomial_sum_eq_add_pow (a b : ℚ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * a^k * b^(n - k) = (a + b)^n := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k _
  ring

end FelsConjectureProof
end
