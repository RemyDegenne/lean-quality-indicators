public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PermutationTriple

variable {n m : ℕ}

@[simp]
theorem cycleCounts_σinf (t : PermutationTriple n) :
    t.cycleCounts.2.2 = orbitCount t.σinf := (rfl)

end PermutationTriple
end TauCeti
end
