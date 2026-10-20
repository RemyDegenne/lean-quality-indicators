@[expose] public section

open Function Matrix

namespace Matrix

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

/-- A matrix `M : Matrix n n R` is positive definite if it is Hermitian
and `xᴴMx` is greater than zero for all nonzero `x`. -/
def PosDef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ ⦃x : n →₀ R⦄, x ≠ 0 → 0 < x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj

end Matrix
end
