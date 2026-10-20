@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc

noncomputable section

namespace MarkoffRiemannRoch

open _root_.FunctionField

namespace FunctionField.Chart

variable (k K : Type*) [Field k] [Field K]
  [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

local instance instDecidableEqRatFuncDivisorFile : DecidableEq k⟮X⟯ := Classical.decEq _

omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_single (v : PlaceA k K) (n : ℤ) :
    deg k K (Finsupp.single v n) = n * placeDegree k K v := by
  simp [deg, Finsupp.sum_single_index]

end FunctionField.Chart
end MarkoffRiemannRoch
end
end
