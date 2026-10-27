@[expose] public section

/-- The Fibonacci-maximal `(2k+1)`-flute, built from `aOdd`. -/
def fibFluteOdd (k : ℕ) : flute (2*k+1) := by
  by_cases hk : k = 0
  · exact ⟨aOdd k 0, fun _ => by simp [hk, aOdd], by simp [hk, aOdd],
      by simp [hk, aOdd], fun _ => by simp⟩
  have pos : ∀ i, aOdd k i > 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hi : i ≥ 2*k
      · unfold aOdd; simp only [hk, ↓reduceIte, ge_iff_le, hi, gt_iff_lt]
        exact ih (i-(2*k)) (by omega)
      · by_cases hi₂ : i < k
        · simp [aOdd, hk, hi, hi₂]
        · simp [aOdd, hk, hi, hi₂]; omega
  have hd : aOdd k 0 = 1 := by simp [hk, aOdd]
  have period : ∀ i, aOdd k i = aOdd k (i+(2*k+1)-1) := by
    intro i
    nth_rw 2 [aOdd]
    simp [hk]
  have div : ∀ i, aOdd k (i+1) ∣ (aOdd k i + aOdd k (i+2)) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hi : i ≥ 2*k
      · have hi₂ : 2*k ≤ i+1 := by omega
        have hi₃ : 2*k ≤ i+2 := by omega
        unfold aOdd; simp only [hk, ↓reduceIte, ge_iff_le, hi₂, hi, hi₃]
        specialize ih (i-(2*k)) (by omega)
        have hi₄ : i-2*k+1 = i+1-2*k := by omega
        have hi₅ : i-2*k+2 = i+2-2*k := by omega
        simpa [hi₄, hi₅] using ih
      · by_cases hi₂ : i+2<k
        · have hi₃ : i+1 < k := by omega
          have hi₄ : i < k := by omega
          have hi₅ : ¬ 2*k ≤ i+1 := by omega
          have hi₆ : ¬ 2*k ≤ i+2 := by omega
          unfold aOdd; simp [hk, hi, hi₂, hi₃, hi₄, hi₅, hi₆]
          ring_nf
          have : 6 + i*2 = (2*i+3)+2+1 := by omega
          rw [this, Nat.fib_add (2*i+3) 2]
          ring_nf
          have h :=
            calc Nat.fib (2+i*2) + Nat.fib (3+i*2) = Nat.fib (i*2+2) + Nat.fib ((i*2+2)+1) := by
                  ring_nf
            _ = Nat.fib ((i*2+2)+2) := by rw [←Nat.fib_add_two]
            _ = Nat.fib (4+i*2) := by ring_nf
          rw [h]
          use 3; omega
        · by_cases hi₃ : i+1 < k
          · have hi₄ : ¬ 2*k ≤ i+1 := by omega
            have hi₅ : ¬ 2*k ≤ i+2 := by omega
            have hi₆ : i < k := by omega
            have hi₇ : 2 * (i+1)+2 = 2*k := by omega
            have hi₈ : 2 * i+2 = 2*k-2 := by omega
            have hi₉ : 1+4*k-2*(i+2) = (2*k-1)+2 := by omega
            unfold aOdd; simp only [hk, ↓reduceIte, ge_iff_le, hi₄, hi₃, hi₇, hi, hi₆, hi₈, hi₅,
              hi₂, hi₉]
            simp only [Nat.fib_add_two, ← add_assoc]
            have : Nat.fib (2*k-2) + Nat.fib (2*k-1) = Nat.fib (2*k) := by
              have : 2*k = (2*k-2)+2 := by omega
              nth_rw 3 [this]
              rw [Nat.fib_add_two]
              congr; omega
            rw [this]
            have : 2*k-1+1=2*k := by omega
            rw [this]
            use 2; omega
          · by_cases hi₄ : i < k
            · have hi₅ : ¬ 2*k ≤ i+1 := by omega
              unfold aOdd; simp only [hk, ↓reduceIte, ge_iff_le, hi₅, hi₃, hi, hi₄, hi₂]
              by_cases hk₁ : k = 1
              · have hi₀ : i = 0 := by omega
                simp only [hk₁, mul_one, Nat.reduceAdd, hi₀, zero_add, Nat.reduceSub, mul_zero,
                  Nat.fib_two, Std.le_refl, ↓reduceIte, tsub_self]
                use 1
                unfold aOdd
                decide
              · have hi₆ : ¬ 2*k ≤ i+2 := by omega
                have hi₇ : 1+4*k-2*(i+1) = (2*k-1)+2 := by omega
                have hi₈ : 2*i+2 = (2*k-1)+1 := by omega
                have hi₉ : 1+4*k-2*(i+2) = 2*k-1 := by omega
                simp only [hi₇, hi₈, hi₆, ↓reduceIte, hi₉]
                use 1; simp [Nat.fib_add_two] ; omega
            · by_cases hi₅ : 2*k ≤ i+2
              · by_cases hi₆ : 2*k ≤ i+1
                · have hi₇ : i+1-2*k = 0 := by omega
                  have hi₈ : i+2-2*k = 1 := by omega
                  unfold aOdd; simp only [hk, ↓reduceIte, ge_iff_le, hi₆, hi₇, hi, hi₄, hi₅, hi₈]
                  unfold aOdd; simp [hk]
                · unfold aOdd; simp only [hk, ↓reduceIte, ge_iff_le, hi₆, hi₃, hi, hi₄, hi₅]
                  have hi₇ : 1+4*k-2*(i+1) = 3 := by omega
                  have hi₈ : 1+4*k-2*i = 5 := by omega
                  have hi₉ : i+2-2*k = 0 := by omega
                  have hk₂ : 0<k := by omega
                  unfold aOdd
                  simp only [hi₇, hi₈, hk, ↓reduceIte, hi₉, ge_iff_le, nonpos_iff_eq_zero,
                    mul_eq_zero, OfNat.ofNat_ne_zero, or_self, hk₂, mul_zero, zero_add, Nat.fib_two]
                  use 3; simp [Nat.fib_add_two]
              · have hi₆ : ¬ 2*k ≤ i+1 := by omega
                unfold aOdd; simp only [hk, ↓reduceIte, ge_iff_le, hi₆, hi₃, hi, hi₄, hi₅, hi₂]
                have hi₇ : 1+4*k-2*(i+1) = 4*k-2*i-1 := by omega
                have hi₈ : 1+4*k-2*i = 4*k-2*i-2+2+1 := by omega
                have hi₉ : 1+4*k-2*(i+2) = 4*k-2*i-3 := by omega
                rw [hi₇, hi₈, hi₉, Nat.fib_add]
                simp only [Nat.fib_add_two, Nat.fib_zero, zero_add, Nat.fib_one, mul_one,
                  Nat.reduceAdd]
                use 3
                rw [add_assoc, add_comm, add_assoc]
                have hi₁₀ : 4*k-2*i-2 = (4*k-2*i-3)+1 := by omega
                have hi₁₁ : 4*k-2*i-3+1+1 = 4*k-2*i-1 := by omega
                rw [hi₁₀, ← Nat.fib_add_two, hi₁₁]
                omega
  exact ⟨aOdd k, pos, hd, period, div⟩

end
