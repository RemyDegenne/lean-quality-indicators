@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra

namespace RightComodule

variable {R : Type u} {C : Type v} {M : Type w}

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid M] [Module R M]

namespace Subcomodule

variable {X : RightComodule R C M}

theorem coaction_mem_range_iff (U : X.Subcomodule) (m : M) :
    X.coaction m ∈ LinearMap.range (U.toSubmodule.subtype.rTensor C) ↔
      ∃ t : U.toSubmodule ⊗[R] C, U.toSubmodule.subtype.rTensor C t = X.coaction m := Iff.rfl

end Subcomodule
end RightComodule
end Coalgebra
end
