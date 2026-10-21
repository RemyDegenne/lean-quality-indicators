namespace OAI

namespace Alternating.Memory

open scoped BigOperators

theorem Block.code_state_cylinder {b K d : ℕ} (hb : 2 ≤ b) (c : Block b K)
    (hd : c.stateDigit = 2 * d) :
    (b : ℝ) * c.code ∈ Set.Icc (2 * (d : ℝ)) (2 * d + 1) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have htail := c.tail_mem hb
  have hm1 := tailBound_lt_one hb
  rw [c.code_formula (by omega)]
  have he : (b : ℝ) *
      (((c.stateDigit : ℝ) + c.leftCode + (b : ℝ)⁻¹ ^ K * c.rightCode) / b) =
      (c.stateDigit : ℝ) + (c.leftCode + (b : ℝ)⁻¹ ^ K * c.rightCode) := by
    field_simp
    ring
  rw [he, hd]
  push_cast
  exact ⟨by linarith [htail.1], by linarith [htail.2]⟩

end Alternating.Memory
end OAI
