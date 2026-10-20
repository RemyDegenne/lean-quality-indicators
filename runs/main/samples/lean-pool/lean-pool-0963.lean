@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

noncomputable section

namespace MarkoffRiemannRoch

open _root_.FunctionField

namespace FunctionField.Chart

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

local instance instDecidableEqRatFuncRRspace : DecidableEq k⟮X⟯ := Classical.decEq _

theorem RRspace_neg_deg_ell {D : DivisorA k K} (h : deg k K D < 0) : ell k K D = 0 := by
  change Module.finrank k (RRspace k K D) = 0
  rw [RRspace_neg_deg k K h]
  exact finrank_bot k K

end FunctionField.Chart
end MarkoffRiemannRoch
end
end
