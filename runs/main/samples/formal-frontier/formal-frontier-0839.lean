@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComodule

section Field

variable {K : Type u} {C : Type v} {M : Type w}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable [AddCommMonoid M] [Module K M]

theorem coefficientSubcoalgebra_fg [Module.Finite K M] (X : RightComodule K C M) :
    X.coefficientSubcoalgebra.toSubmodule.FG := by
  simpa only [coefficientSubcoalgebra_toSubmodule] using coefficientSpan_fg X

end Field
end Coalgebra.RightComodule
end
