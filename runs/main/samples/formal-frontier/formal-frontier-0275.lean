set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR uG

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] {R : Type uR}

section Semiring

variable [Semiring R]

@[simp]
theorem diagonalPairUnit_val (A : GL X R) (D : GL Y R) :
    (diagonalPairUnit A D : Matrix (X ⊕ Y) (X ⊕ Y) R) =
      Matrix.fromBlocks (A : Matrix X X R) 0 0 (D : Matrix Y Y R) := by
  have hswap :
      (reindexEquiv R (Equiv.sumComm Y X) (stabilize (Y := X) D) :
        Matrix (X ⊕ Y) (X ⊕ Y) R) = Matrix.fromBlocks 1 0 0 D := by
    ext row col
    rcases row with row | row <;> rcases col with col | col <;>
      simp [Matrix.one_apply]
  change Matrix.fromBlocks (A : Matrix X X R) 0 0 1 * _ = _
  rw [hswap, Matrix.fromBlocks_multiply]
  simp

end Semiring
end Matrix.GeneralLinearGroup
end
