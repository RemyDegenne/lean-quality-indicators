@[expose] public section

namespace Lean4LPD.DiscardWitness

open Finset PauliString

theorem discardedStep_pauliNorm : pauliNorm (discardedStep Gs angles 2 1 (toMatrix P) 0) = 1 := by
  rw [pauliNorm_discardedStep, trotterStepTraj_zero, traj_two, Q_highNorm]

end Lean4LPD.DiscardWitness
end
