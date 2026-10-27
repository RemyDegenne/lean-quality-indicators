@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

noncomputable section

namespace FunctionField

open Chart

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]

namespace WeilDifferential

variable {k K}

/-- The divisor of a nonzero intrinsic Weil differential. -/
noncomputable def divOmega (omega : WeilDifferential k K) (homega : IsNonzero omega) :
    Divisor k K :=
  divisorEquivChart k K <|
    Chart.WeilDifferential.divOmega (toChart omega) ((isNonzero_toChart omega).mp homega)

end WeilDifferential
end FunctionField
end
end
