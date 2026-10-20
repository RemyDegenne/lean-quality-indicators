@[expose] public section

open scoped BigOperators

namespace EGZ.FlagDecomposition.Iteration

open DecompositionParameters

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    {g : ℕ → ℕ} (P : NormalizedOperationParameters d g) (ε : ℝ)

namespace BoundedState

variable {P ε} {i : ℕ} (s : BoundedState (f := f) P ε i)

/-- Advance a bounded state using a certified progress step and a radius bound. -/
noncomputable def advance {t : State p d f} (hε : 0 < ε)
    (D : Progress s.toState t ε (stageScale d ε i) g)
    (hR : t.radius ≤ P.radiusGrowth s.radius) : BoundedState (f := f) P ε (i + 1) where
  toState := t
  card_bound := D.card_le.trans
    (by simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left 2 s.card_bound)
  radius_bound := by
    change t.radius ≤ P.radiusGrowth^[i + 1] 1
    rw [Function.iterate_succ_apply']
    exact hR.trans (P.radiusGrowth_growing.1 s.radius_bound)
  mass_loss_bound := by
    rw [prefixBudget_succ]
    have hcoef : 0 ≤ ε * stageScale d ε i ^ 2 + (3 : ℝ) ^ (d + 1) * stageScale d ε i := by
      have := (stageScale_pos d hε i).le
      positivity
    have hM : (s.decomposition.retainedMass : ℝ) ≤ natMass f := by exact_mod_cast s.mass_le_input
    have hs := mul_le_mul_of_nonneg_left hM hcoef
    have hl := D.mass_loss_le
    change (s.decomposition.retainedMass : ℝ) - t.decomposition.retainedMass ≤ _ at hl
    nlinarith [s.mass_loss_bound]

end BoundedState
end EGZ.FlagDecomposition.Iteration
end
