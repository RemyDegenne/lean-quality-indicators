@[expose] public section

namespace RS

universe u

open Equiv

/-- The complex group algebra of the symmetric group `S_n`. -/
abbrev SymGroupAlgebra (n : ℕ) : Type :=
  MonoidAlgebra ℂ (Equiv.Perm (Fin n))

end RS
end
