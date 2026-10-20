@[expose] public section

universe uR uC uD uV uW

open scoped TensorProduct

namespace Coalgebra.RightComodule

variable {R : Type uR} {C : Type uC} {D : Type uD}

variable {V : Type uV} {W : Type uW}

variable [CommSemiring R]

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid D] [Module R D] [Coalgebra R D]

variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

theorem externalTensorCoaction_regular :
    externalTensorCoaction (regular R C) (regular R D) =
      Coalgebra.comul (R := R) (A := C ⊗[R] D) := by
  simpa only [externalTensorCoaction, regular,
    _root_.TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_eq,
    _root_.TensorProduct.AlgebraTensorModule.map_eq] using
    (_root_.TensorProduct.comul_def (R := R) (S := R) (A := C) (B := D)).symm

end Coalgebra.RightComodule
end
