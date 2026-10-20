set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR uG

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] {R : Type uR}

section Ring

variable [Ring R]

theorem diagonalPairUnit_inv_pair (g : GL X R) :
    diagonalPairUnit g g⁻¹ = blockDiagonalUnit g := by
  apply Units.ext
  simp [diagonalPairUnit_val, blockDiagonalUnit]

end Ring
end Matrix.GeneralLinearGroup
end
