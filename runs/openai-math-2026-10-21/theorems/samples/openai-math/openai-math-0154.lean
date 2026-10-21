namespace OAI

open Set

open scoped BigOperators

namespace SimplexChord

variable {ι : Type*} [Fintype ι]

theorem endpoints_iff (b x : ι → ℝ) (hb : ∑ i, b i = 0)
    {s : ℝ} (hs : 0 ≤ s) :
    (x ∈ standardSimplex ∧ (fun i => x i + s * b i) ∈ standardSimplex) ↔
      (∀ i, s * max 0 (-b i) ≤ x i) ∧ ∑ i, x i = 1 := by
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨fun i => ?_, hx.2⟩
    rcases le_total 0 (-b i) with hi | hi
    · rw [max_eq_right hi]
      have h := hy.1 i
      linarith
    · rw [max_eq_left hi, mul_zero]
      exact hx.1 i
  · rintro ⟨hx, hsum⟩
    have hxnonneg : ∀ i, 0 ≤ x i := fun i =>
      (mul_nonneg hs (le_max_left _ _)).trans (hx i)
    refine ⟨⟨hxnonneg, hsum⟩, ⟨fun i => ?_, ?_⟩⟩
    · have hle := mul_le_mul_of_nonneg_left (le_max_right 0 (-b i)) hs
      have h := hx i
      nlinarith
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, hb, mul_zero,
        add_zero]

end SimplexChord
end OAI
