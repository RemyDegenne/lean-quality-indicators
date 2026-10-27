@[expose] public noncomputable section

universe u' u v w

variable {ι R V E F V₁ V₂ V₃ : Type*}

open Fin

open LineDeriv

namespace LineDeriv

variable [LineDeriv E V₁ V₂] [LineDeriv E V₂ V₃]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]

section TensorProduct

variable [CommRing R] [AddCommGroup E] [Module R E]
  [Module R V₂] [Module R V₃]
  [LineDerivAdd E V₂ V₃] [LineDerivAdd E V₁ V₂]
  [LineDerivSMul R E V₂ V₃] [LineDerivLeftSMul R E V₁ V₂] [LineDerivLeftSMul R E V₂ V₃]

open TensorProduct

variable (R) in
/-- The second derivative in terms `lineDerivOp` as a bilinear map.

Mainly used to give an abstract definition of the Laplacian. -/
def bilinearLineDerivTwo (f : V₁) : E →ₗ[R] E →ₗ[R] V₃ :=
  LinearMap.mk₂ R (∂_{·} <| ∂_{·} f) (by simp [lineDerivOp_left_add])
    (by simp [lineDerivOp_left_smul]) (by simp [lineDerivOp_left_add, lineDerivOp_add])
    (by simp [lineDerivOp_left_smul, lineDerivOp_smul])

end TensorProduct
end LineDeriv
end
