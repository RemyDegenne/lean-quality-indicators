set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  {R : Type v} [Ring R]

theorem upperUnit_add (a b : Matrix ι ι R) :
    upperUnit (a + b) = upperUnit a * upperUnit b := by
  apply Units.ext
  simp [upperUnit, Matrix.fromBlocks_multiply, add_comm]

end Matrix.GeneralLinearGroup
end
