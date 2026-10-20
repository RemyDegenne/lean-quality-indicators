@[expose] public section

namespace OddCase

open Nat Fin Finset

variable (n : ℕ) (F : Finset ℕ)

variable {n F} {x : ℤ}

@[simp] lemma tup_natAdd_two : tup n F x (natAdd n 2) = (x - 1) ^ 5 := by simp [tup]

end OddCase
end
