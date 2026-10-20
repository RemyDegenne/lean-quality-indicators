set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR uG

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] {R : Type uR}

section Ring

variable [Ring R]

@[simp]
theorem rectangularUpperUnit_mul_apply_inr {columns : Type*}
    (C : Matrix X Y R) (matrix : Matrix (X ⊕ Y) columns R)
    (row : Y) (column : columns) :
    (((rectangularUpperUnit C : Matrix (X ⊕ Y) (X ⊕ Y) R) * matrix)
      (Sum.inr row) column) = matrix (Sum.inr row) column := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

end Ring
end Matrix.GeneralLinearGroup
end
