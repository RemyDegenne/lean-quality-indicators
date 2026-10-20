public section

namespace TauCeti

namespace IntegralLattice

variable (n : ℕ)

variable {n}

variable (n)

variable {n}

@[simp]
theorem checkerboardVector_apply [NeZero n] (i : Fin n) :
    checkerboardVector n i = if i = checkerboardLastIndex n then 1 else 0 := by
  rw [checkerboardVector, Pi.single_apply]

end IntegralLattice
end TauCeti
end
