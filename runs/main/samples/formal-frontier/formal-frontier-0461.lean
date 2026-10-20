@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComodule

section Field

variable {K : Type u} {C : Type v} {M : Type w}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable [AddCommMonoid M] [Module K M]

theorem subtype_lTensor_comp_restrictCoalgebra_coaction (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    D.subtype.toLinearMap.lTensor M ∘ₗ (X.restrictCoalgebra D h).coaction = X.coaction :=
  X.subtype_lTensor_comp_coactionCodRestrict D h

end Field
end Coalgebra.RightComodule
end
