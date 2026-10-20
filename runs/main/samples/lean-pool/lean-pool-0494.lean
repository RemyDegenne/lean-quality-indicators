@[expose] public section

open Polynomial BigOperators Nat

noncomputable section

namespace Problem4

variable (n : ℕ) (hn : 2 ≤ n)

lemma boxPlusCoeff_shift_identity
    (n : ℕ) (hn : 2 ≤ n) (a b : ℕ → ℝ) (m : ℕ) (hm : m ≤ n - 1)
    (ha0 : a 0 = 0) :
    boxPlusCoeff n a b (m + 1) =
    boxPlusCoeff (n - 1) (fun k ↦ a (k + 1)) (fun k ↦ (↑(n - k) : ℝ) / ↑n * b k) m := by
  unfold boxPlusCoeff
  -- The i=0 term on LHS vanishes since a(0) = 0. Shift the index.
  conv_lhs => rw [Finset.sum_range_succ']
  simp only [ha0, zero_mul, mul_zero, add_zero, Nat.sub_zero]
  -- Now both sides are sums over Finset.range (m+1). Match term by term.
  apply Finset.sum_congr rfl
  intro i hi; rw [Finset.mem_range] at hi
  -- Simplify natural number subtractions on the LHS
  have h1 : m + 1 - (i + 1) = m - i := by omega
  have h2 : n - (i + 1) = n - 1 - i := by omega
  have h3 : n - (m - i) = n - m + i := by omega
  have h4 : n - (m + 1) = n - 1 - m := by omega
  have h5 : (n - 1 : ℕ) - (m - i) = n - 1 - m + i := by omega
  rw [h1, h2, h3, h4, h5]
  -- Use factorial identities: (n-m+i)! = (n-m+i)*(n-m+i-1)! and n! = n*(n-1)!
  have h_fact_nmi : ((n - m + i).factorial : ℝ) =
      (↑(n - m + i) : ℝ) * ((n - m + i - 1).factorial : ℝ) :=
    factorial_pred_mul_real (n - m + i) (by omega)
  have h_nmi_eq : n - m + i - 1 = n - 1 - m + i := by omega
  have h_n_fact : (n.factorial : ℝ) = (↑n : ℝ) * ((n - 1).factorial : ℝ) :=
    factorial_pred_mul_real n (by omega)
  rw [h_fact_nmi, h_nmi_eq, h_n_fact]
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : ((n - 1).factorial : ℝ) ≠ 0 := factorial_ne_zero_real _
  have : ((n - 1 - m).factorial : ℝ) ≠ 0 := factorial_ne_zero_real _
  field_simp

end Problem4
end
end
