public section

open Coalgebra TensorProduct WithConv

open scoped RingTheory.LinearMap

variable {R S A B C ι : Type*} [CommSemiring R]

namespace LinearMap

section Semiring

variable [Semiring A] [Algebra R A] [AddCommMonoid C] [Module R C]

section CoalgebraStruct

variable [CoalgebraStruct R C]

variable [Semiring B] [Algebra R B]

lemma algHom_comp_convMul_distrib (h : A →ₐ B) (f g : WithConv (C →ₗ[R] A)) :
    h.toLinearMap.comp (f * g).ofConv =
      (toConv (h.toLinearMap.comp f.ofConv) * toConv (h.toLinearMap.comp g.ofConv)).ofConv := by
  simp [convMul_def, map_comp, ← comp_assoc, AlgHom.comp_mul']

end CoalgebraStruct
end Semiring
end LinearMap
end
