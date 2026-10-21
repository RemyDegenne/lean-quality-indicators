namespace OAI

namespace MetricKMedianRecovery.PolytopeCertificate

open Matrix

open scoped BigOperators

variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]

omit [Fintype R] in
lemma slack_region_iff (A : Matrix R V ℤ) (b : R → ℤ) (B H : ℤ) (y : Option V → ℝ) :
    y ∈ region (fun r j => (slackMatrix A r j:ℝ)) (fun r => (slackBounds b B H r:ℝ)) ↔
      (0 ≤ y none ∧ y none ≤ (H:ℝ)) ∧
      (∀ j, -(B:ℝ) ≤ y (some j) ∧ y (some j) ≤ (B:ℝ)) ∧
      (∀ r, (∑ j, (A r j:ℝ)*y (some j)) ≤ (b r:ℝ)+y none) := by
  have he (r : R) : (∑ j, (slackMatrix A (.inl r) j:ℝ)*y j) =
      -y none+∑ j, (A r j:ℝ)*y (some j) := by
    simp [Fintype.sum_option,slackMatrix]
  have hb (s : Bool) (j : Option V) :
      (∑ k, (slackMatrix A (.inr (s,j)) k:ℝ)*y k) = if s then y j else -y j := by
    cases s <;> simp [slackMatrix]
  constructor
  · intro h
    have h0 := h (.inr (false,none))
    have hH := h (.inr (true,none))
    rw [hb] at h0 hH
    refine ⟨?_,?_,?_⟩
    · simpa only [Bool.false_eq_true,Bool.true_eq,ite_false,ite_true,slackBounds,
        Int.cast_zero,neg_nonpos] using And.intro h0 hH
    · intro j
      have hl := h (.inr (false,some j))
      have hu := h (.inr (true,some j))
      simp only [hb,slackBounds,Bool.false_eq_true,ite_false,ite_true] at hl hu
      exact ⟨by linarith,hu⟩
    · intro r
      have hh := h (.inl r)
      rw [he] at hh
      change -y none+(∑ j, (A r j:ℝ)*y (some j)) ≤ (b r:ℝ) at hh
      linarith
  · rintro ⟨ht,hx,ha⟩ r
    cases r with
    | inl r =>
      rw [he]
      change _ ≤ (b r:ℝ)
      linarith [ha r]
    | inr p =>
      rcases p with ⟨s,j⟩
      rw [hb]
      cases j with
      | none =>
        cases s
        · simpa only [Bool.false_eq_true,ite_false,slackBounds,Int.cast_zero,neg_nonpos] using ht.1
        · exact ht.2
      | some j =>
        cases s
        · change -y (some j) ≤ (B:ℝ)
          linarith [(hx j).1]
        · exact (hx j).2

end MetricKMedianRecovery.PolytopeCertificate
end OAI
