@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero Additive

open Polynomial BigOperators Submodule IntermediateField Ideal FunctionField

noncomputable section

namespace FunctionField.Chart

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

variable [IsFullConstantField k K]

local instance instDecidableEqPlaceARam : DecidableEq (PlaceA k K) := Classical.decEq _

local instance instDecidableEqRatFuncRam : DecidableEq k⟮X⟯ := Classical.decEq _

/-- `t` as an element of the valuation subring at infinity. -/
noncomputable def tA : inftyValuationSubring k :=
  ⟨tRatFunc k, by
    rw [Valuation.mem_valuationSubring_iff]
    dsimp [tRatFunc]
    rw [RatFunc.inftyValuation.X_inv k]
    exact WithZero.exp_le_exp.mpr (show (-1 : ℤ) ≤ 0 by omega)⟩

end FunctionField.Chart
end
end
