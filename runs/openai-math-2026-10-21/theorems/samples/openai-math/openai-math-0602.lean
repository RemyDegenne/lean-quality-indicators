namespace OAI

namespace Ostmann

open scoped Classical

theorem movingSlotWeight_real_cell_difference {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : ∀ {n}, MovingSlotData σ n → ℝ → ℝ → ℂ)
    (E : ∀ {n}, MovingSlotData σ n → ℝ → ℝ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL YL XR : ℕ)
    (hres : (XL : ℤ) ≡ (YL : ℤ) [ZMOD movingTopPeriod value hvalue childBound pivotBound T hf])
    (hcell : rootCellCode (movingTopRootCuts value hvalue childBound pivotBound T hf XR) (XL : ℝ) =
      rootCellCode (movingTopRootCuts value hvalue childBound pivotBound T hf XR) (YL : ℝ)) :
    ‖recursiveTransferWeight (movingSlotSystem value childBound pivotBound) (movingRealLeaf F)
        (movingSlotCutoff value childBound pivotBound (movingRealExtra E)) n ⟨n, T, XL, XR⟩ t -
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound) (movingRealLeaf F)
        (movingSlotCutoff value childBound pivotBound (movingRealExtra E)) n ⟨n, T, YL, XR⟩ t‖ ≤
      ‖movingRealWeight value F E T XL XR - movingRealWeight value F E T YL XR‖ := by
  rw [movingSlotWeight_real_factor value hvalue childBound pivotBound F E T t hT hf,
    movingSlotWeight_real_factor value hvalue childBound pivotBound F E T t hT hf,
    movingArithmeticIndicator_cells value hvalue childBound pivotBound T hf XL YL XR hres hcell,
    ← mul_sub, norm_mul]
  by_cases hs : T.ArithmeticSupport value childBound pivotBound YL XR
  · simp only [movingArithmeticIndicator, ite_eq_left hs, norm_one, one_mul, le_refl]
  · simp only [movingArithmeticIndicator, ite_eq_right hs, norm_zero, zero_mul, norm_nonneg]

end Ostmann
end OAI
