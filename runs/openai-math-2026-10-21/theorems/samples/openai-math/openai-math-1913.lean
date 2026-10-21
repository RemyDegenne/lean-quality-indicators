namespace OAI

noncomputable section

open scoped BigOperators Classical ComplexOrder

open Matrix

namespace BinaryCoordinateSweeps.Density

variable {I : Type*} [Fintype I] [DecidableEq I]

variable {A : Type*} [Fintype A] [DecidableEq A]

lemma symmetricProjector_identity (n : ℕ) (x : (Fin n → A) → ℂ)
    (hx : ∀ w v, wordCounts w = wordCounts v → x w = x v) :
    (symmetricProjector n).mulVec x = x := by
  funext w
  change (∑ v, (if wordType n w = wordType n v then
    ((Nat.multinomial Finset.univ (wordType n w).val : ℝ)⁻¹ : ℂ) else 0) * x v) = x w
  have he (v) : (if wordType n w = wordType n v then
      ((Nat.multinomial Finset.univ (wordType n w).val : ℝ)⁻¹ : ℂ) else 0) * x v =
      if wordType n v = wordType n w then
        ((Nat.multinomial Finset.univ (wordType n w).val : ℝ)⁻¹ : ℂ) * x w else 0 := by
    by_cases h : wordType n w = wordType n v
    · rw [ite_eq_left h, ite_eq_left h.symm, hx w v ((wordType_eq_iff n w v).mp h)]
    · simp [h, Ne.symm h]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun v : Fin n → A => wordType n v = wordType n w)).card =
      Nat.multinomial Finset.univ (wordType n w).val := by
    rw [← Fintype.card_subtype, card_wordType]
  rw [hc]
  have hn : (Nat.multinomial Finset.univ (wordType n w).val : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ (wordType n w).val))
  push_cast
  field_simp

end BinaryCoordinateSweeps.Density
end
end OAI
