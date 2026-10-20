public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PermutationTriple

variable {n : ℕ}

variable (t : PermutationTriple n)

variable (τ : Perm (Fin n))

variable {t}

variable (t)

@[simp] theorem monodromyGroup_rot : (rot t).monodromyGroup = t.monodromyGroup := by
  rw [rot, monodromyGroup_swap1Inf, monodromyGroup_swap01]

end PermutationTriple
end TauCeti
end
