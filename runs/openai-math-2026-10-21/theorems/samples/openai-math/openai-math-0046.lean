namespace OAI

open Set MeasureTheory Function

open scoped ENNReal

namespace CircleDomainRigidity.FiniteTransfer

theorem summable_grid_pair_probabilities {S : Type*} {h : ℝ} (hh : 0 < h)
    (a b : S → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s)
    (ha2 : Summable (fun s => a s ^ 2)) (hb2 : Summable (fun s => b s ^ 2)) :
    Summable (fun s => min 1 (a s / h) * min 1 (b s / h)) := by
  have hs := (LengthArea.summable_mul_of_squares ha2 hb2).div_const (h * h)
  apply hs.of_norm_bounded
  intro s
  have hma : 0 ≤ min 1 (a s / h) := le_min zero_le_one (div_nonneg (ha s) hh.le)
  have hmb : 0 ≤ min 1 (b s / h) := le_min zero_le_one (div_nonneg (hb s) hh.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hma hmb)]
  calc
    _ ≤ (a s / h) * (b s / h) :=
      mul_le_mul (min_le_right _ _) (min_le_right _ _) hmb (div_nonneg (ha s) hh.le)
    _ = (a s * b s) / (h * h) := by ring

end CircleDomainRigidity.FiniteTransfer
end OAI
