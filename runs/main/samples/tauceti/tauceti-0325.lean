public section

open scoped TensorProduct

universe u v w

namespace Ideal

section Right

variable (R : Type u) (A : Type v) {B : Type w}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

@[simp]
theorem rightTensorIdeal_iSup {ι : Sort*} (I : ι → Ideal B) :
    rightTensorIdeal R A (⨆ i, I i) = ⨆ i, rightTensorIdeal R A (I i) :=
  Ideal.map_iSup
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom I

end Right
end Ideal
end
