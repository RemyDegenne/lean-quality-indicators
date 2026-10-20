public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PermutationTriple

variable {n m : ℕ}

@[simp]
theorem cycleData_σ1 (t : PermutationTriple n) :
    t.cycleData.2.1 = t.σ1.partition.parts := by
  simp [cycleData, Equiv.Perm.fullCycleType_def]

end PermutationTriple
end TauCeti
end
