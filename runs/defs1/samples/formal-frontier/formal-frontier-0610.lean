@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComodule

section Field

variable {K : Type u} {C : Type v} {M : Type w}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable [AddCommMonoid M] [Module K M]

/-- The right comodule on the same module with coacting coalgebra corestricted to `D`. -/
noncomputable def restrictCoalgebra (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    RightComodule K D M where
  coaction := X.coactionCodRestrict D h
  coassoc := by exact coactionCodRestrict_coassoc X D h
  counit_comp := by exact coactionCodRestrict_counit_comp X D h

end Field
end Coalgebra.RightComodule
end
