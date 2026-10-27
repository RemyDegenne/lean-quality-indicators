set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix

variable {K F : Type} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] {r : ℕ}

theorem gram_zero (β : Module.Basis (Fin r) K F) : gram β (0 : F) = 0 := by
  ext i j
  simp [gram_apply]

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
end
