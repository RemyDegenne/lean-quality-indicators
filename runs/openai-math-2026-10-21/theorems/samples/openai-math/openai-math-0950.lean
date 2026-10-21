namespace OAI

namespace Balanced.CandidatePrescribed

noncomputable section

open scoped Classical

open Finset PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_codes_le (old : Finset (Direction F)) (j : ℕ) (hj : j ≤ 4) :
    (tupleCodesWithOldCount old j).card ≤
      (4096 * (old.card + 1) ^ 4) * Fintype.card F ^ (4 - j) := by
  have hchoose : Nat.choose 4 j ≤ 16 := by
    interval_cases j <;> decide
  have hpow : old.card ^ j ≤ (old.card + 1) ^ 4 := by
    calc
      old.card ^ j ≤ (old.card + 1) ^ j := Nat.pow_le_pow_left (by omega) j
      _ ≤ (old.card + 1) ^ 4 := Nat.pow_le_pow_right (by omega) hj
  have hdir : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
    have hq : 0 < Fintype.card F := Fintype.card_pos
    simp only [Direction, Fintype.card_option]
    omega
  have htwo : 2 ^ (4 - j) ≤ 16 := by
    calc
      2 ^ (4 - j) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 16 := rfl
  calc
    (tupleCodesWithOldCount old j).card ≤
        16 * (Nat.choose 4 j * old.card ^ j * Fintype.card (Direction F) ^ (4-j)) :=
      card_tupleCodesWithOldCount_le old j
    _ ≤ 16 * (16 * (old.card + 1) ^ 4 * (2 * Fintype.card F) ^ (4-j)) := by
      gcongr
    _ = 256 * (old.card + 1) ^ 4 * (2 ^ (4-j) * Fintype.card F ^ (4-j)) := by
      rw [Nat.mul_pow]
      ring
    _ ≤ 256 * (old.card + 1) ^ 4 * (16 * Fintype.card F ^ (4-j)) := by
      gcongr
    _ = _ := by ring

end
end Balanced.CandidatePrescribed
end OAI
