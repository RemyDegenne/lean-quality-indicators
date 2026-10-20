set_option warningAsError true

@[expose] public section

namespace Nat.DivisionGrowth

theorem affine_lower_bound (u : ℕ → ℕ) (s n : ℕ) (hs : 0 < s) (hsn : s < n)
    (hstep : ∀ m, n * (u m / s) ≤ u (m + 1)) (m : ℕ) :
    ((n : ℚ) / s) ^ m * ((u 0 : ℚ) -
      (n : ℚ) * ((s - 1 : ℕ) : ℚ) / ((n : ℚ) - s)) +
      (n : ℚ) * ((s - 1 : ℕ) : ℚ) / ((n : ℚ) - s) ≤ (u m : ℚ) := by
  let ratio : ℚ := (n : ℚ) / s
  let offset : ℚ := (n : ℚ) * ((s - 1 : ℕ) : ℚ) / ((n : ℚ) - s)
  have hratio : 0 ≤ ratio := by
    dsimp [ratio]
    positivity
  have hstepQ (i : ℕ) : ratio * ((u i : ℚ) - offset) + offset ≤
      (u (i + 1) : ℚ) := affine_step u s n hs hsn hstep i
  change ratio ^ m * ((u 0 : ℚ) - offset) + offset ≤ (u m : ℚ)
  induction m with
  | zero => simp
  | succ i hi =>
      calc
        ratio ^ (i + 1) * ((u 0 : ℚ) - offset) + offset =
            ratio * (ratio ^ i * ((u 0 : ℚ) - offset) + offset - offset) +
              offset := by rw [pow_succ]; ring
        _ ≤ ratio * ((u i : ℚ) - offset) + offset := by
          apply add_le_add_left
          exact mul_le_mul_of_nonneg_left (sub_le_sub_right hi offset) hratio
        _ ≤ (u (i + 1) : ℚ) := hstepQ i

end Nat.DivisionGrowth
end
