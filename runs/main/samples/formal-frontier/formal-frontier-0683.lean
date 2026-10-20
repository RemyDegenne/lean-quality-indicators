set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR uG

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] {R : Type uR}

section Semiring

variable [Semiring R]

@[simp]
theorem diagonalPairUnit_one_right (A : GL X R) :
    diagonalPairUnit A (1 : GL Y R) = stabilize (Y := Y) A := by
  simp [diagonalPairUnit]

end Semiring
end Matrix.GeneralLinearGroup
end
