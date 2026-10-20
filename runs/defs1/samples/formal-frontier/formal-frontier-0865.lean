@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComodule

section CommSemiring

variable {K : Type u} {C : Type v} {M : Type w}

variable [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]

variable [AddCommMonoid M] [Module K M]

/-- The submodule spanned by all coefficients of a specified right coaction. -/
def coefficientSpan (X : RightComodule K C M) : Submodule K C :=
  Submodule.span K (Set.range (Function.uncurry X.coefficient))

end CommSemiring
end Coalgebra.RightComodule
end
