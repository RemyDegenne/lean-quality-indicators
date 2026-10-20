@[expose] public section

namespace AspPerm

variable (τ : AspPerm)

lemma a_step_gt_iff (a b : ℤ) : τ.s a b < τ.s (a + 1) b ↔ b ≤ τ⁻¹ a := by
  -- Proof written by GPT-5.
  have hiff := τ.a_step_one_iff a b
  have hstep : τ.s a b ≤ τ.s (a + 1) b ∧ τ.s (a + 1) b ≤ τ.s a b + 1 :=
    τ.s.a_step a b
  constructor
  · intro h
    exact hiff.mp (by omega)
  · intro h
    have hs := hiff.mpr h
    omega

end AspPerm
end
