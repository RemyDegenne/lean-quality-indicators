namespace OAI

namespace Falconer.Regularization

open Set

variable {d : ℕ}

theorem unitProfile_range {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (p : CellPath d) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    unitProfile L F N B p u ∈ Icc (0 : ℝ) (d : ℝ) := by
  have h := unitProfile_increment hN hB hL F p (u := 0) (v := u) (by rfl) hu.1 hu.2
  rw [unitProfile_zero,sub_zero,sub_zero] at h
  exact ⟨h.1,h.2.trans (mul_le_of_le_one_right (Nat.cast_nonneg d) hu.2)⟩

end Falconer.Regularization
end OAI
