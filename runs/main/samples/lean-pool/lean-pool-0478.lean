@[expose] public section

namespace Lean4LPD.DiscardWitness

open Finset PauliString

theorem boundary_eq_zero : trotterTraj Gs angles 2 1 (toMatrix P) 2 = 0 := by
  simpa only [Nat.one_mul, step_one] using
    trotterTraj_at_boundary Gs angles 2 1 (toMatrix P) 1 (by norm_num)

end Lean4LPD.DiscardWitness
end
