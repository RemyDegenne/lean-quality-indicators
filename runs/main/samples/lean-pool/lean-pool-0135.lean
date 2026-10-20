@[expose] public section

open Finset MeasureTheory Set

namespace QuadraticCarleson

theorem packetPoint_abs_sub_right_ge
    {N : ℕ} {k : ℤ} {τ : ℝ} {j : ℕ}
    (hN : 100 ≤ N) (hk : k ∈ paperBohrIndices N)
    (hτ : τ ∈ Ico (1 / 4 : ℝ) (1 / 2 : ℝ))
    (hj : k.toNat + 1 ≤ j) :
    ((j - (k.toNat + 1) : ℕ) : ℝ) + 1 / 2 ≤
      |(k : ℝ) + τ - (j : ℝ)| := by
  have hkcast : (k.toNat : ℝ) = k := paperBohrIndex_cast_toNat hN hk
  rw [abs_of_nonpos]
  · rw [Nat.cast_sub hj, Nat.cast_add, hkcast]
    linarith [hτ.2]
  · have hjR : k + 1 ≤ (j : ℝ) := by
      calc
        k + 1 = (k.toNat : ℝ) + 1 := by rw [hkcast]
        _ ≤ (j : ℝ) := by exact_mod_cast hj
    have hdiff : (0 : ℝ) ≤ (j - (k.toNat + 1) : ℕ) := by positivity
    linarith [hτ.2, hjR]

end QuadraticCarleson
end
