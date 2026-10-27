@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

noncomputable section

namespace FunctionField.Chart

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

variable [IsFullConstantField k K]

local instance instDecidableEqRatFuncWeil : DecidableEq k⟮X⟯ := Classical.decEq _

attribute [local instance] adeleFiltAddCommGroup adeleFiltModule

namespace WeilDifferential

variable {k K}

/-- A Weil differential is nonzero. -/
def IsNonzero (ω : WeilDifferential k K) : Prop := ω.toFun ≠ 0

end WeilDifferential
end FunctionField.Chart
end
end
