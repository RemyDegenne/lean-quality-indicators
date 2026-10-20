set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace LinearEquiv

universe u

@[simp]
theorem coefficientRowCompletionOfStableRangeCondition_apply_zero
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin (n + 1) → R)
    (ha : Bass.IsRightUnimodular a) {s : ℕ}
    (hs : Bass.StableRangeCondition R s) (hsn : s ≤ n)
    (x : Fin (n + 1) → R) :
    coefficientRowCompletionOfStableRangeCondition R n a ha hs hsn x 0 = a ⬝ᵥ x := by
  simp [coefficientRowCompletionOfStableRangeCondition,
    Bass.kernelProdEquivOfIsRightUnimodular_symm_snd]

end LinearEquiv
end
