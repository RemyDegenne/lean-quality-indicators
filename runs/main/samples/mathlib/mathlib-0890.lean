@[expose] public section

open Fin Nat Function

namespace Fin

variable {n m : ℕ}

section Succ

@[simp] lemma castAdd_inj {a b : Fin m} : castAdd n a = castAdd n b ↔ a = b := by simp [Fin.ext_iff]

end Succ
end Fin
end
