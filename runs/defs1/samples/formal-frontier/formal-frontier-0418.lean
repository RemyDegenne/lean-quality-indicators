set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uR uS uT

section Blocks

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
  {R : Type uR} [Ring R]

/-- The upper unitriangular block matrix with upper-right block `a`. -/
def upperUnit (a : Matrix ι ι R) : (BlockMatrix (ι := ι) (R := R))ˣ where
  val := Matrix.fromBlocks 1 a 0 1
  inv := Matrix.fromBlocks 1 (-a) 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

end Blocks
end Matrix.GeneralLinearGroup
end
