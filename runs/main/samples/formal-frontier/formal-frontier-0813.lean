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

universe uM uN

variable {M : Type uM} {N : Type uN}

variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

theorem externalTensor_coaction_apply (X : RightComodule R C M)
    (Y : RightComodule R D N) (t : M ⊗[R] N) :
    (externalTensor X Y).coaction t = externalTensorCoaction X Y t := by
  rfl

end Coalgebra.RightComodule
end
