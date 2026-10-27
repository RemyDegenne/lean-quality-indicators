@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

open IsDedekindDomain

open scoped BigOperators nonZeroDivisors Polynomial

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Mathlib's chosen quadratic extension of the finite field `K`. -/
abbrev SquareExtension := FiniteField.Extension K p 2

end
end BGS.HasseWeil
end
