set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  {R : Type v} [Ring R]

theorem lowerUnit_zero :
    lowerUnit (0 : Matrix ι ι R) = 1 := by
  apply Units.ext
  simp [lowerUnit]

end Matrix.GeneralLinearGroup
end
