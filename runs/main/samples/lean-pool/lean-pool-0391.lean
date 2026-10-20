@[expose] public section

namespace AtanasovRanganathan.ConfigurationFive

open Utilities

open Certificate

open Certificate.ExplicitPotential

open Certificate.DegenerateSpec

@[simp] theorem headContribution_same (L h : ℕ) :
    headContribution L h h = 0 := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · simp [headContribution, hL]
  · have hLast : L - 1 < L := by omega
    simp [headContribution, hL.ne',
      SubdivisionArithmetic.step_zero_of_lt hLast]

end AtanasovRanganathan.ConfigurationFive
end
