public section

namespace TauCeti

open Function Set

namespace DynkinType

namespace TypeC

variable {n : ℕ}

/-- The character-lattice coordinates of the classical basis vector `e_a` of type `Cₙ`: its
pairings `⟨e_a, αₖ^∨⟩ = [a = k] - [a = k + 1]` against the simple coroots. -/
def weight (n a : ℕ) : Fin n → ℤ :=
  fun k => (if a = (k : ℕ) then 1 else 0) - (if a = (k : ℕ) + 1 then 1 else 0)

end TypeC
end DynkinType
end TauCeti
end
