set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR uG

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] {R : Type uR}

section Ring

variable [Ring R]

theorem triangularUnit_eq_diagonal_mul_upper (A : GL X R)
    (B : Matrix X Y R) (D : GL Y R) :
    triangularUnit A B D =
      diagonalPairUnit A D *
        rectangularUpperUnit (((A⁻¹ : GL X R) : Matrix X X R) * B) := by
  apply Units.ext
  simp only [triangularUnit_val, Units.val_mul, diagonalPairUnit_val,
    rectangularUpperUnit_val, Matrix.fromBlocks_multiply, mul_one, Matrix.mul_zero,
    add_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, Matrix.fromBlocks_inj,
    and_self, and_true, true_and]
  rw [← Matrix.mul_assoc, ← Units.val_mul]
  simp

end Ring
end Matrix.GeneralLinearGroup
end
