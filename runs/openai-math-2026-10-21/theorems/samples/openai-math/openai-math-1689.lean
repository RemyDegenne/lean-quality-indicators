namespace OAI

namespace Ostmann

open scoped Classical

theorem movingSlotWeight_arithmeticSupport {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ)
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t ≠ 0) :
    T.ArithmeticSupport value childBound pivotBound XL XR := by
  let a := topGiantInput XL XR
  have hL : (HistoryFormula.prime false).value (fun b => (a b : ℚ)) = (XL : ℚ) := by
    simp [a, topGiantInput]
  have hR : (HistoryFormula.prime true).value (fun b => (a b : ℚ)) = (XR : ℚ) := by
    simp [a, topGiantInput]
  exact (T.formulaNodes_iff value hvalue childBound pivotBound hf XL XR _ _ a hL hR).mp
    (movingSlotWeight_formulaNodes value hvalue childBound pivotBound F extra T t hT hf
      XL XR _ _ a hL hR hw)

end Ostmann
end OAI
