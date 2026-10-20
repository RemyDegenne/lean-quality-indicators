@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra

namespace RightComodule

variable {R : Type u} {C : Type v} {M : Type w}

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid M] [Module R M]

@[simp] theorem regular_coaction (c : C) :
    (regular R C).coaction c = comul (R := R) c := rfl

end RightComodule
end Coalgebra
end
