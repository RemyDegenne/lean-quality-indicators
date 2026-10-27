set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR uG

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] {R : Type uR}

section Ring

variable [Ring R]

/-- The rectangular upper unipotent matrix, with inverse upper block `-C`. -/
def rectangularUpperUnit (C : Matrix X Y R) : GL (X ⊕ Y) R where
  val := Matrix.fromBlocks 1 C 0 1
  inv := Matrix.fromBlocks 1 (-C) 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

end Ring
end Matrix.GeneralLinearGroup
end
