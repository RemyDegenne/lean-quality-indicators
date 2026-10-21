namespace OAI

noncomputable section

open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma zeroCornerRow_commutator_bound (q a b x : E) (δ γ : ℝ) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hq : ‖q‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hqc : ‖q * x - x * q‖ ≤ γ) (hac : ‖a * x - x * a‖ ≤ δ)
    (hbc : ‖b * x - x * b‖ ≤ δ) :
    ∀ n i, ‖zeroCornerRow q a b n i * x - x * zeroCornerRow q a b n i‖ ≤
      (n : ℝ) * δ + γ := by
  intro n
  induction n with
  | zero => intro i; simpa only [zeroCornerRow, Nat.cast_zero, zero_mul, zero_add] using hqc
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change ‖b * x - x * b‖ ≤ _
      have hn : 0 ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg n) hδ
      exact hbc.trans (by rw [Nat.cast_add, Nat.cast_one]; nlinarith)
    · change ‖(a * zeroCornerRow q a b n j) * x - x * (a * zeroCornerRow q a b n j)‖ ≤ _
      have hp := row_product_commutator_le a (zeroCornerRow q a b n j) x ha
        (zeroCornerRow_norm_le q a b hq ha hb n j)
      have hi := ih j
      rw [Nat.cast_add, Nat.cast_one]
      linarith

end WeakPureInfiniteness
end
end OAI
