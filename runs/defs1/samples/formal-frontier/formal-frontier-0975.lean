@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComodule

section Field

variable {K : Type u} {C : Type v} {M : Type w}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable [AddCommMonoid M] [Module K M]

/-- The linear corestriction of a coaction through the tensor inclusion of a subcoalgebra. -/
noncomputable def coactionCodRestrict (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    M →ₗ[K] M ⊗[K] D :=
  X.coaction.codLift (D.subtype.toLinearMap.lTensor M)
    (by
      let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
      exact Module.Flat.lTensor_preserves_injective_linearMap
        (R := K) (M := M) D.subtype.toLinearMap D.subtype_injective) h

end Field
end Coalgebra.RightComodule
end
