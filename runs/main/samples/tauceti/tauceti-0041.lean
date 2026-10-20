public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PermutationTriple

variable {m n : ℕ}

theorem genus_of_degree_one (t : PermutationTriple 1) : t.genus = 0 := by
  rw [Subsingleton.elim t 1, genus_def, eulerChar_one]
  norm_num

end PermutationTriple
end TauCeti
end
